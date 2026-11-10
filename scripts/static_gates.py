#!/usr/bin/env python3
"""Cheap static CI gates for the Lean formalization (no Lean, no lake).

Gates (see .local plan "PR 1"; select with ``--gate``):

  G1  forbidden tokens in Lean code (comments, docstrings, strings, raw
      strings and char literals masked): sorry, admit, sorryAx, axiom
      declarations, native_decide, decide +native, native := true,
      ofReduceBool/ofReduceNat, addDecl/axiomDecl, implemented_by, extern,
      unsafe, opaque, debug.skipKernelTC, and metaprogramming commands
      (run_cmd, #eval, elab, macro, syntax, initialize, ...).  Warns on
      maxHeartbeats 0.
  G2  import layering: Statements/ChN.lean imports only modules on a frozen
      allowlist and never a *Proofs module; library files import Statements
      modules only on a frozen allowlist; bare ``import Mathlib`` only in files
      on a frozen allowlist.
  G3  statement index <-> ledger <-> COVERAGE <-> SOURCE-ISSUES consistency.
  G4  (static part) Lean names cited in the ledger and COVERAGE resolve to a
      declaration found by a namespace-aware scan of Formalization/.
      FUTURE WORK: the compiled step (emit ``#check @Name`` lines and run
      ``lake env lean`` on them after ``lake build``) is not implemented here.
  G6  every declaration lies under a ``StatisticalRL`` namespace (the prefix
      audited by Audit.lean).

Frozen allowlists live in ``scripts/gates/*.txt`` (one key per line, optional
`` | count=N``).  They may only shrink: an entry that now occurs less often is
reported as stale and fails, and a missing list file fails.
``--write-allowlists`` rewrites them shrink-only; adding entries needs
``--allow-grow`` (and a justification in the PR), and the G1 list never grows.

G1 is a cheap first filter; the axiom audit in Audit.lean is the authority.

Python 3.9 compatible, standard library only.
"""

import argparse
import json
import os
import re
import sys
from collections import Counter

GATES = ("G1", "G2", "G3", "G4", "G6")

# ---------------------------------------------------------------------------
# Lean lexing helpers


def mask_lean(text):
    """Return (code, comments).

    ``code`` has the same length and line structure as ``text`` with every
    comment, docstring and string literal replaced by spaces (newlines kept).
    ``comments`` is a list of (start, end, body) for each block comment
    (including docstrings ``/-- -/`` and module docs ``/-! -/``).
    """
    out = list(text)
    comments = []
    i, n = 0, len(text)

    def blank(a, b):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    def scan_code(i, interp):
        """Lex code from ``i``.  With ``interp`` stop at the ``}`` closing a
        string interpolation and return its index; otherwise return ``n``."""
        depth = 0
        while i < n:
            c = text[i]
            if interp and c == "{":
                depth += 1
                i += 1
            elif interp and c == "}":
                if depth == 0:
                    return i
                depth -= 1
                i += 1
            elif c == "-" and text.startswith("--", i):
                j = text.find("\n", i)
                j = n if j < 0 else j
                blank(i, j)
                i = j
            elif c == "/" and text.startswith("/-", i):
                depth_c, j = 1, i + 2
                while j < n and depth_c:
                    if text.startswith("/-", j):
                        depth_c += 1
                        j += 2
                    elif text.startswith("-/", j):
                        depth_c -= 1
                        j += 2
                    else:
                        j += 1
                comments.append((i, j, text[i:j]))
                blank(i, j)
                i = j
            elif c == "'" and not _ident_char_before(text, i):
                m = CHAR_LIT_RE.match(text, i)
                if m:
                    blank(i, m.end())
                    i = m.end()
                else:
                    i += 1
            elif c == "r" and not _ident_char_before(text, i) and RAW_OPEN_RE.match(text, i):
                hashes = RAW_OPEN_RE.match(text, i).group(1)
                start = i + 2 + len(hashes)
                j = text.find('"' + hashes, start)
                j = n if j < 0 else j + 1 + len(hashes)
                blank(i, j)
                i = j
            elif c == '"':
                i = scan_string(i)
            else:
                i += 1
        return n

    def scan_string(i):
        """Blank the string literal at ``i``; code inside ``{...}`` of an
        interpolated string (``s!"…"``, ``m!"…"``, ``throwError "…"``, …) is
        lexed as code and stays visible to the gates."""
        interp = _interpolated_string_at(text, i)
        seg, j = i, i + 1
        while j < n and text[j] != '"':
            if text[j] == "\\":
                j += 2
            elif interp and text[j] == "{":
                blank(seg, j + 1)
                k = scan_code(j + 1, True)
                seg = k
                j = k + 1
            else:
                j += 1
        j = min(j + 1, n)
        blank(seg, j)
        return j

    scan_code(0, False)
    return "".join(out), comments


# Lean char literal: 'x', '\n', '\'', '\x41', '\u{3b1}'.
CHAR_LIT_RE = re.compile(r"'(?:\\(?:x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f]+\}|.)|[^\\'\n])'")
# Raw string opener: r"...", r#"..."#, r##"..."## ...
RAW_OPEN_RE = re.compile(r'r(#*)"')


INTERP_BEFORE_RE = re.compile(
    r"(?:!|\b(?:throwError|throwErrorAt|logInfo|logWarning|logError|logInfoAt|logWarningAt|logErrorAt)\s*)$")


def _interpolated_string_at(text, i):
    return bool(INTERP_BEFORE_RE.search(text[max(0, i - 40):i]))


def _ident_char_before(text, i):
    if i == 0:
        return False
    p = text[i - 1]
    return p.isalnum() or p in "_'!?." or "⁰" <= p <= "₟"


def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


_ID_START = "A-Za-z_\u00c0-\u1fff\u2100-\u214f"
_ID_CHAR = "\\w'!?\u00c0-\u1fff\u2070-\u209f\u2100-\u214f"
# Dotted identifier.  A dot must be followed by another component, so the
# universe suffix in `Foo.{u}` is not captured.
IDENT = ("[" + _ID_START + "][" + _ID_CHAR + "]*(?:\\.[" + _ID_START + "][" + _ID_CHAR + "]*)*")
UNIV = r"(?:\.\{[^}]*\})?"
DECL_KW = (
    "theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque|"
    "example|alias|irreducible_def"
)
# Commands that create declarations or run code at elaboration time.  They
# are scanned too: G6 flags them outside `StatisticalRL`, G1 flags the
# code-running ones everywhere.
CMD_KW = (
    "deriving\\s+instance|macro_rules|macro|syntax|notation|infixl|infixr|infix|prefix|postfix|"
    "elab_rules|elab|initialize|builtin_initialize|declare_syntax_cat"
)
MODIFIERS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
# Attribute lists with up to two levels of nested brackets, e.g.
# `@[simp, aesop safe (rule_sets := [X])]`.
ATTR = r"(?:@\[(?:[^\[\]]|\[(?:[^\[\]]|\[[^\[\]]*\])*\])*\]\s*)*"
# `open Foo in` / `set_option x y in` prefixes, possibly on the same line.
IN_PREFIX = r"(?:(?:open|set_option)\b[^\n]*?\bin\s+)*"
DECL_RE = re.compile(
    r"^[ \t]*" + IN_PREFIX + ATTR + IN_PREFIX + MODIFIERS +
    r"(?P<kind>class\s+inductive|" + DECL_KW + r"|" + CMD_KW + r")(?![\w'])\s*(?P<name>" + IDENT + r")?",
    re.M,
)
NS_RE = re.compile(r"^[ \t]*(namespace|section|end)\b[ \t]*(" + IDENT + r")?", re.M)
STRUCTLIKE = {"structure", "class", "inductive"}
CMD_KINDS = {"deriving instance", "macro_rules", "macro", "syntax", "notation", "infixl", "infixr", "infix",
             "prefix", "postfix", "elab_rules", "elab", "initialize", "builtin_initialize",
             "declare_syntax_cat", "irreducible_def"}


def scan_decls(text, code=None):
    """Namespace-aware declaration scan.

    Returns list of dicts {name, short, kind, line, ns, pos}.  ``ns`` is the
    namespace in force at the declaration (``""`` at top level).
    """
    if code is None:
        code, _ = mask_lean(text)
    events = []
    for m in NS_RE.finditer(code):
        events.append((m.start(), "ns", m))
    for m in DECL_RE.finditer(code):
        events.append((m.start(), "decl", m))
    events.sort(key=lambda e: e[0])
    stack = []  # list of (kind, name) where kind is namespace/section
    decls = []
    for pos, typ, m in events:
        if typ == "ns":
            kw, name = m.group(1), m.group(2) or ""
            if kw == "namespace":
                stack.append(("namespace", name))
            elif kw == "section":
                stack.append(("section", name))
            else:  # end
                # `end X.Y` closes possibly several namespace components;
                # we treat it as closing one scope opened with that name.
                if stack:
                    stack.pop()
            continue
        kind = " ".join(m.group("kind").split())
        if kind == "class inductive":
            kind = "inductive"
        name = m.group("name") or ""
        if kind == "example":
            continue
        if kind in CMD_KINDS and kind not in ("irreducible_def",):
            name = ""  # syntax/macro names are not declaration names we track
        ns = ".".join(n for k, n in stack if k == "namespace" and n)
        if name.startswith("_root_."):
            full = name[len("_root_."):]
        elif name:
            full = ns + "." + name if ns else name
        else:
            full = ""
        decls.append({
            "name": full,
            "short": name,
            "kind": kind,
            "line": line_of(code, pos),
            "ns": ns,
            "pos": pos,
            "root": name.startswith("_root_."),
        })
    return decls


# ---------------------------------------------------------------------------
# Tree access


class Tree(object):
    def __init__(self, root):
        self.root = os.path.abspath(root)
        self._cache = {}

    def path(self, *parts):
        return os.path.join(self.root, *parts)

    def rel(self, p):
        return os.path.relpath(p, self.root).replace(os.sep, "/")

    def lean_files(self):
        res = []
        base = self.path("Formalization")
        for d, _, files in os.walk(base):
            for f in files:
                if f.endswith(".lean"):
                    res.append(self.rel(os.path.join(d, f)))
        for extra in ("Formalization.lean", "Audit.lean"):
            if os.path.exists(self.path(extra)):
                res.append(extra)
        return sorted(res)

    def read(self, rel):
        if rel not in self._cache:
            with open(self.path(rel), encoding="utf-8") as fh:
                text = fh.read()
            code, comments = mask_lean(text)
            self._cache[rel] = (text, code, comments)
        return self._cache[rel]

    def gate_list(self, name):
        p = self.path("scripts", "gates", name)
        if not os.path.exists(p):
            return None
        items = []
        with open(p, encoding="utf-8") as fh:
            for ln in fh:
                ln = ln.strip()
                if ln and not ln.startswith("#"):
                    items.append(ln)
        return items

    def write_gate_list(self, name, header, counts):
        d = self.path("scripts", "gates")
        if not os.path.isdir(d):
            os.makedirs(d)
        with open(os.path.join(d, name), "w", encoding="utf-8") as fh:
            for h in header:
                fh.write("# " + h + "\n")
            for k in sorted(counts):
                if counts[k] <= 0:
                    continue
                fh.write(k + ("" if counts[k] == 1 else " | count=%d" % counts[k]) + "\n")


def parse_gate_lines(items):
    counts = Counter()
    for it in items:
        key, sep, c = it.rpartition(" | count=")
        if sep and c.isdigit():
            counts[key] += int(c)
        else:
            counts[it] += 1
    return counts


class Result(object):
    def __init__(self, gate):
        self.gate = gate
        self.errors = []
        self.warnings = []
        self.info = []

    def err(self, msg):
        self.errors.append(msg)

    def warn(self, msg):
        self.warnings.append(msg)


class Options(object):
    def __init__(self, write=False, allow_grow=False):
        self.write = write
        self.allow_grow = allow_grow


def allowlist(res, tree, opts, listname, header, found, what, growable=True):
    """Compare found exceptions with the frozen allowlist ``scripts/gates/<listname>``.

    ``found`` is a list of (key, location) pairs; a key may occur several
    times and the allowlist stores a count per key.  In check mode a key that
    occurs more often than allowlisted fails, and so does an allowlisted key
    that now occurs less often (stale: shrink the list).  A missing list file
    fails.  In write mode the list is rewritten shrink-only; growth needs
    ``--allow-grow`` and is never permitted when ``growable`` is False.
    """
    cnt = Counter(k for k, _ in found)
    locs = {}
    for k, loc in found:
        locs.setdefault(k, []).append(loc)
    items = tree.gate_list(listname)
    allowed = parse_gate_lines(items) if items is not None else None
    path = "scripts/gates/" + listname
    if opts.write:
        base = allowed if allowed is not None else Counter()
        new = Counter()
        for k in set(cnt) | set(base):
            c, a = cnt.get(k, 0), base.get(k, 0)
            if c <= a:
                new[k] = c
            elif opts.allow_grow and growable:
                new[k] = c
                res.warn("GROWING %s: %s (%d -> %d)" % (path, k, a, c))
            else:
                new[k] = a
                why = ("this list never grows" if not growable else "growth requires --allow-grow")
                res.err("%s not added to %s (%s): %s at %s" % (what, path, why, k, ", ".join(locs[k][:5])))
        tree.write_gate_list(listname, header, new)
        res.info.append("%s written: %d entries" % (listname, sum(new.values())))
        return
    if allowed is None:
        res.err("missing allowlist %s (%d %s present)" % (path, sum(cnt.values()), what))
        return
    for k in sorted(cnt):
        c, a = cnt[k], allowed.get(k, 0)
        if c > a:
            for loc in locs[k]:
                res.err("%s: %s not on frozen allowlist %s (%s; %d found, %d allowed)"
                        % (loc, what, path, k, c, a))
    for k in sorted(allowed):
        c, a = cnt.get(k, 0), allowed[k]
        if c < a:
            res.err("stale entry in %s (%d allowed, %d present; shrink the list): %s" % (path, a, c, k))
    res.info.append("%s: %d allowlisted" % (listname, sum(allowed.values())))


# ---------------------------------------------------------------------------
# G1 forbidden tokens

# Reserved command keywords (never identifiers): matched anywhere in masked
# code, so several commands on one line do not hide them.  `syntax` also
# occurs inside quotations, so it is only matched at the start of a line.
G1_CMDS = (r"run_cmd|run_elab|run_meta|#eval!?|#exit|elab_rules|elab|macro_rules|macro|initialize|"
           r"builtin_initialize|declare_syntax_cat")
G1_PATTERNS = [
    ("sorry", re.compile(r"(?<![\w.'])sorry(?![\w'])")),
    ("admit", re.compile(r"(?<![\w.'])admit(?![\w'])")),
    ("sorryAx", re.compile(r"\bsorryAx\b")),
    ("axiom declaration", re.compile(r"(?<![\w.'#])axiom(?![\w'])")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("decide +native", re.compile(r"\bdecide\s*\+\s*native\b")),
    ("native := true", re.compile(r"\bnative\s*:=\s*true\b")),
    ("ofReduceBool/ofReduceNat", re.compile(r"\b(?:ofReduceBool|ofReduceNat|reduceBool|reduceNat)\b")),
    ("addDecl/axiomDecl", re.compile(r"\b(?:addDecl|addAndCompile|axiomDecl)\b")),
    ("implemented_by", re.compile(r"\bimplemented_by\b")),
    ("extern", re.compile(r"(?<![\w.'])extern(?![\w'])")),
    ("unsafe", re.compile(r"(?<![\w.'])unsafe(?![\w'])")),
    ("opaque", re.compile(r"(?<![\w.'])opaque(?![\w'])")),
    ("debug.skipKernelTC", re.compile(r"debug\.skipKernelTC")),
    ("metaprogramming command", re.compile(r"(?<![\w.'#])(?:" + G1_CMDS + r")(?![\w'!])")),
    ("metaprogramming command", re.compile(
        r"^[ \t]*" + IN_PREFIX + ATTR + MODIFIERS + r"syntax(?![\w'!])", re.M)),
]
G1_WARN = re.compile(r"maxHeartbeats\s+0\b")
# The axiom audit itself is one `run_cmd` in Audit.lean.  Exactly that many
# metaprogramming commands are exempt there; any further one fails.
AUDIT_RUN_CMD_EXEMPT = 1


def gate_g1(tree, opts):
    res = Result("G1")
    files = tree.lean_files()
    if not files:
        res.err("no Lean files found under Formalization/ (wrong --root?)")
        return res
    found = []
    for rel in files:
        _, code, _ = tree.read(rel)
        exempt = AUDIT_RUN_CMD_EXEMPT if rel == "Audit.lean" else 0
        for label, pat in G1_PATTERNS:
            for m in pat.finditer(code):
                if label == "metaprogramming command" and exempt and m.group(0).strip() == "run_cmd":
                    exempt -= 1
                    continue
                found.append(("%s: %s" % (rel, label), "%s:%d" % (rel, line_of(code, m.start()))))
        for m in G1_WARN.finditer(code):
            res.warn("%s:%d: set_option maxHeartbeats 0" % (rel, line_of(code, m.start())))
    allowlist(res, tree, opts, "g1_forbidden_tokens.txt",
              ["G1 frozen exceptions: '<file>: <token>[ | count=N]'. Never grows; may only shrink."],
              found, "forbidden token", growable=False)
    res.info.append("%d Lean files scanned" % len(files))
    return res


# ---------------------------------------------------------------------------
# G2 import layering

IMPORT_RE = re.compile(r"^\s*import\s+([^\n]+)", re.M)
STATEMENT_FILE_RE = re.compile(r"^Formalization/Statements/Ch(\d+)\.lean$")
PROOFS_FILE_RE = re.compile(r"^Formalization/Statements/Ch(\d+)Proofs\.lean$")


def imports_of(tree, rel):
    _, code, _ = tree.read(rel)
    mods = []
    for m in IMPORT_RE.finditer(code):
        mods.extend(m.group(1).split())
    return mods


def gate_g2(tree, opts):
    res = Result("G2")
    stmt_edges, lib_to_stmt, bare = [], [], []
    for rel in tree.lean_files():
        if not rel.startswith("Formalization/"):
            continue
        mods = imports_of(tree, rel)
        if "Mathlib" in mods:
            bare.append((rel, rel))
        if STATEMENT_FILE_RE.match(rel):
            for m in mods:
                if m.startswith("Formalization."):
                    if m.endswith("Proofs"):
                        res.err("%s imports proof module %s (statement index must not import proofs)"
                                % (rel, m))
                    stmt_edges.append(("%s -> %s" % (rel, m), rel))
        elif not rel.startswith("Formalization/Statements/"):
            for m in mods:
                if m.startswith("Formalization.Statements."):
                    lib_to_stmt.append(("%s -> %s" % (rel, m), rel))
    allowlist(res, tree, opts, "g2_statement_imports.txt",
              ["G2 frozen imports of Statements/ChN.lean: '<file> -> <module>'. May only shrink."],
              stmt_edges, "Statements/ChN.lean import")
    allowlist(res, tree, opts, "g2_library_to_statements.txt",
              ["G2 frozen library -> Statements import edges. May only shrink."],
              lib_to_stmt, "library -> Statements import")
    allowlist(res, tree, opts, "g2_bare_mathlib.txt",
              ["G2 frozen files with bare `import Mathlib`. May only shrink."], bare, "bare `import Mathlib`")
    return res


# ---------------------------------------------------------------------------
# G3 statement index consistency

PROP_DEF_RE = re.compile(
    r"^[ \t]*" + ATTR + MODIFIERS + r"def\s+(" + IDENT + r")(?:\.\{[^}]*\})?\s*:\s*Prop\s*:=", re.M)
HOLDS_RE = re.compile(r"^[ \t]*" + ATTR + MODIFIERS + r"theorem\s+(" + IDENT + r")", re.M)
# The whole header after `theorem X_holds` up to `:=` must be `: X` (universe
# suffixes allowed), so a wrapper such as `X -> False` is rejected.
HOLDS_HEADER_RE = re.compile(r"\s*" + UNIV + r"\s*:\s*(" + IDENT + r")" + UNIV + r"\s*")
TEX_RANGE_RE = re.compile(r"\.tex:\s*\d+\s*(?:[–—\-]|--)\s*\d+")
CID_RE = re.compile(r"(?<![\w#])C(\d{1,3})(?![\w])")


def docstring_before(text, comments, pos):
    """Return the docstring body attached to a declaration at ``pos``."""
    best = None
    for (a, b, body) in comments:
        if b <= pos and body.startswith("/--"):
            between = text[b:pos]
            if re.fullmatch(r"\s*(?:@\[[^\]]*\]\s*)*", between):
                best = body
    return best


def source_issue_ids(tree):
    p = tree.path("docs", "SOURCE-ISSUES.md")
    if not os.path.exists(p):
        return None
    with open(p, encoding="utf-8") as fh:
        txt = fh.read()
    ids = set(re.findall(r'id="C(\d+)"', txt))
    ids |= set(re.findall(r"^#+\s*Candidate\s+C(\d+)\b", txt, re.M))
    return ids


def statement_entries(tree):
    """Map full name -> dict for every `def X : Prop` in Statements/ChN.lean."""
    entries = {}
    for rel in tree.lean_files():
        if not STATEMENT_FILE_RE.match(rel):
            continue
        text, code, comments = tree.read(rel)
        decls = scan_decls(text, code)
        for m in PROP_DEF_RE.finditer(code):
            short = m.group(1)
            ns = ""
            for d in decls:
                if d["pos"] <= m.start() and d["kind"] == "def" and d["short"] == short:
                    ns = d["ns"]
            full = ns + "." + short if ns else short
            entries[full] = {
                "short": short, "file": rel, "line": line_of(code, m.start()),
                "doc": docstring_before(text, comments, m.start()),
            }
    return entries


def gate_g3(tree, opts):
    res = Result("G3")
    entries = statement_entries(tree)
    issue_ids = source_issue_ids(tree)
    if issue_ids is None:
        res.err("docs/SOURCE-ISSUES.md missing")
        issue_ids = set()

    # (a) docstrings, (d) C-ids in docstrings
    for full, e in sorted(entries.items()):
        loc = "%s:%d" % (e["file"], e["line"])
        if e["doc"] is None:
            res.err("%s: statement entry %s has no docstring" % (loc, e["short"]))
            continue
        if not TEX_RANGE_RE.search(e["doc"]):
            res.err("%s: docstring of %s cites no `.tex:a-b` line range" % (loc, e["short"]))
        for cid in CID_RE.findall(e["doc"]):
            if cid not in issue_ids:
                res.err("%s: docstring of %s cites C%s, which is not an anchor in docs/SOURCE-ISSUES.md"
                        % (loc, e["short"], cid))

    # (b) exactly one X_holds per entry, no orphans; (f) no proofs in index
    holds = {}
    for rel in tree.lean_files():
        m = PROOFS_FILE_RE.match(rel)
        if m:
            text, code, _ = tree.read(rel)
            for hm in HOLDS_RE.finditer(code):
                name = hm.group(1)
                stop = code.find(":=", hm.end())
                header = code[hm.end():stop if stop >= 0 else len(code)]
                hh = HOLDS_HEADER_RE.fullmatch(header)
                typ = hh.group(1) if hh else " ".join(header.split())
                if name.endswith("_holds"):
                    holds.setdefault(name[:-len("_holds")], []).append(
                        (rel, line_of(code, hm.start()), typ))
        if STATEMENT_FILE_RE.match(rel):
            _, code, _ = tree.read(rel)
            for dm in re.finditer(r"^[ \t]*" + ATTR + MODIFIERS + r"(theorem|lemma)\b", code, re.M):
                res.err("%s:%d: statement index contains a %s (proofs belong in ChNProofs.lean)"
                        % (rel, line_of(code, dm.start()), dm.group(1)))
    shorts = {}
    for full, e in entries.items():
        shorts.setdefault(e["short"], []).append(full)
    for full, e in sorted(entries.items()):
        exp_chapter = re.match(r".*/Ch(\d+)\.lean$", e["file"]).group(1)
        hs = holds.get(e["short"], [])
        if len(hs) != 1:
            res.err("%s:%d: entry %s has %d `theorem %s_holds` declarations in Statements/ChNProofs.lean "
                    "(expected exactly 1)" % (e["file"], e["line"], e["short"], len(hs), e["short"]))
            continue
        rel, ln, typ = hs[0]
        if not rel.endswith("Ch%sProofs.lean" % exp_chapter):
            res.err("%s:%d: %s_holds is not in Ch%sProofs.lean" % (rel, ln, e["short"], exp_chapter))
        if not (typ == e["short"] or ("." + full).endswith("." + typ)):
            res.err("%s:%d: %s_holds must have type exactly `%s`; its header is `%s`"
                    % (rel, ln, e["short"], e["short"], typ))
    for short, hs in sorted(holds.items()):
        if short not in shorts:
            for rel, ln, _ in hs:
                res.err("%s:%d: orphan theorem %s_holds has no statement entry %s" % (rel, ln, short, short))

    # (c) ledger
    ledger_p = tree.path("docs", "named-result-status.json")
    if not os.path.exists(ledger_p):
        res.err("docs/named-result-status.json missing")
        return res
    with open(ledger_p, encoding="utf-8") as fh:
        ledger = json.load(fh)
    seen = {}
    for section in ("certified_named_results", "proved_variants"):
        for rec in ledger.get(section, []):
            rname = rec.get("name", "?")
            st = rec.get("lean_statement")
            if not st:
                res.err("ledger %s record %r has no lean_statement" % (section, rname))
                continue
            if st not in entries:
                res.err("ledger %s record %r: lean_statement %s is not a `def ... : Prop` in "
                        "Formalization/Statements/ChN.lean" % (section, rname, st))
            pf = rec.get("lean_statement_proof")
            if pf != st + "_holds":
                res.err("ledger %s record %r: lean_statement_proof %r != %r"
                        % (section, rname, pf, st + "_holds"))
            seen.setdefault(st, []).append(rname)
            for cid in CID_RE.findall(rec.get("statement_scope", "") or ""):
                if cid not in issue_ids:
                    res.err("ledger record %r cites C%s, not an anchor in docs/SOURCE-ISSUES.md"
                            % (rname, cid))
    for st, names in sorted(seen.items()):
        if len(names) > 1:
            res.err("ledger: lean_statement %s is used by %d records: %s" % (st, len(names), names))

    # (d) C-ids cited in COVERAGE
    cov_p = tree.path("docs", "COVERAGE.md")
    if os.path.exists(cov_p):
        with open(cov_p, encoding="utf-8") as fh:
            for i, ln in enumerate(fh, 1):
                for cid in CID_RE.findall(ln):
                    if cid not in issue_ids:
                        res.err("docs/COVERAGE.md:%d cites C%s, not an anchor in docs/SOURCE-ISSUES.md"
                                % (i, cid))
    else:
        res.err("docs/COVERAGE.md missing")
    res.info.append("%d statement entries, %d with _holds, %d ledger records"
                    % (len(entries), sum(1 for e in entries.values() if e["short"] in holds),
                       sum(len(v) for v in seen.values())))
    return res


# ---------------------------------------------------------------------------
# G4 cited names resolve (static)

LEDGER_NAME_FIELDS = ("lean_statement", "lean_statement_proof", "lean_export", "component_exports")
CITED_RE = re.compile(r"StatisticalRL(?:\.[\w'Ͱ-Ͽ⁰-₟]+)+")


def all_decls(tree):
    names, structs = {}, set()
    for rel in tree.lean_files():
        text, code, _ = tree.read(rel)
        for d in scan_decls(text, code):
            if not d["name"]:
                continue
            names.setdefault(d["name"], []).append("%s:%d" % (rel, d["line"]))
            if d["kind"] in STRUCTLIKE:
                structs.add(d["name"])
    return names, structs


def cited_names(tree):
    cited = []  # (name, where)
    ledger_p = tree.path("docs", "named-result-status.json")
    if os.path.exists(ledger_p):
        with open(ledger_p, encoding="utf-8") as fh:
            ledger = json.load(fh)
        for section in ("certified_named_results", "proved_variants"):
            for rec in ledger.get(section, []):
                for f in LEDGER_NAME_FIELDS:
                    v = rec.get(f)
                    vals = v if isinstance(v, list) else [v]
                    for x in vals:
                        if isinstance(x, str):
                            for n in CITED_RE.findall(x):
                                cited.append((n.rstrip("."), "ledger %r.%s" % (rec.get("name"), f)))
        # Lean refutations of printed statements (the site's refuted markers come from this field)
        for key, rec in sorted((ledger.get("printed_refuted") or {}).items()):
            if key.startswith("_") or not isinstance(rec, dict):
                continue
            for x in rec.get("lean") or []:
                if isinstance(x, str):
                    cited.append((x, "ledger printed_refuted[%r].lean" % key))
    cov_p = tree.path("docs", "COVERAGE.md")
    if os.path.exists(cov_p):
        with open(cov_p, encoding="utf-8") as fh:
            for i, ln in enumerate(fh, 1):
                for bt in re.findall(r"`([^`]+)`", ln):
                    for n in CITED_RE.findall(bt):
                        cited.append((n.rstrip("."), "docs/COVERAGE.md:%d" % i))
    return cited


def gate_g4(tree, opts):
    res = Result("G4")
    names, structs = all_decls(tree)
    cited = cited_names(tree)
    first = {}
    for n, where in cited:
        if n in names:
            continue
        parent = n.rsplit(".", 1)[0]
        if parent in structs:  # structure field / constructor / generated projection
            continue
        first.setdefault(n, where)
    found = []
    for n, where in sorted(first.items()):
        short = n.rsplit(".", 1)[-1]
        cands = [k for k in names if k.endswith("." + short)][:3]
        found.append((n, "%s (same short name: %s)" % (where, ", ".join(cands) or "none")))
    allowlist(res, tree, opts, "g4_unresolved_names.txt",
              ["G4 frozen cited names not found by the static declaration scan. May only shrink."],
              found, "cited Lean name not declared in Formalization/")
    res.info.append("%d cited names checked (%d distinct)" % (len(cited), len(set(n for n, _ in cited))))
    res.info.append("compiled `#check` step (G4') not implemented: future work")
    return res


# ---------------------------------------------------------------------------
# G6 audit scope


def in_scope(name):
    return name == "StatisticalRL" or name.startswith("StatisticalRL.")


NAMELESS_OK = {"instance", "alias"}
# A declaration keyword after other code on the same line (e.g.
# `end StatisticalRL theorem t ...`) is not seen by DECL_RE; flag it.
MIDLINE_DECL_RE = re.compile(
    r"(?<![\w.'#@\[])(theorem|lemma|def|abbrev|structure|inductive|axiom|opaque|irreducible_def)(?![\w'])")
LINE_START_DECL_RE = re.compile(r"^[ \t]*" + IN_PREFIX + ATTR + IN_PREFIX + MODIFIERS + r"(?:class\s+)?$")


def midline_decls(code):
    res = []
    for m in MIDLINE_DECL_RE.finditer(code):
        ls = code.rfind("\n", 0, m.start()) + 1
        before = code[ls:m.start()]
        if LINE_START_DECL_RE.match(before):
            continue
        # `@[...]` attribute lists spanning the previous text on this line
        if re.fullmatch(r"\s*(?:" + ATTR + r")\s*", before):
            continue
        res.append((m.group(1), line_of(code, m.start())))
    return res


def gate_g6(tree, opts):
    res = Result("G6")
    found = []
    for rel in tree.lean_files():
        if not rel.startswith("Formalization/"):
            continue
        text, code, _ = tree.read(rel)
        for kw, ln in midline_decls(code):
            found.append(("%s: mid-line `%s` (unparsed declaration)" % (rel, kw), "%s:%d" % (rel, ln)))
        for d in scan_decls(text, code):
            loc = "%s:%d" % (rel, d["line"])
            if d["kind"] in CMD_KINDS and d["kind"] != "irreducible_def":
                if not in_scope(d["ns"]):
                    found.append(("%s: `%s` command outside StatisticalRL" % (rel, d["kind"]), loc))
                continue
            if not d["name"]:
                if d["kind"] in NAMELESS_OK:
                    if not in_scope(d["ns"]):
                        found.append(("%s: anonymous %s outside StatisticalRL" % (rel, d["kind"]), loc))
                else:
                    # fail closed: a declaration whose name the scanner cannot read
                    found.append(("%s: unparsed `%s` declaration name" % (rel, d["kind"]), loc))
                continue
            if not in_scope(d["name"]):
                found.append(("%s: %s" % (rel, d["name"]), loc))
    allowlist(res, tree, opts, "g6_namespace_exceptions.txt",
              ["G6 frozen declarations outside namespace StatisticalRL (not audited). May only shrink."],
              found, "declaration outside namespace StatisticalRL (not covered by Audit.lean)")
    return res


GATE_FUNCS = {"G1": gate_g1, "G2": gate_g2, "G3": gate_g3, "G4": gate_g4, "G6": gate_g6}


def run(root, gates, write=False, out=sys.stdout, allow_grow=False):
    tree = Tree(root)
    opts = Options(write=write, allow_grow=allow_grow)
    failed = False
    for g in gates:
        if write and g == "G3":
            continue  # G3 has no allowlist
        try:
            res = GATE_FUNCS[g](tree, opts)
        except Exception as exc:  # report and keep running the other gates
            res = Result(g)
            res.err("gate crashed: %s: %s" % (type(exc).__name__, exc))
        status = "FAIL" if res.errors else "ok"
        out.write("%s %s (%d errors, %d warnings)%s\n" % (
            g, status, len(res.errors), len(res.warnings), " [write mode]" if write else ""))
        for i in res.info:
            out.write("  info: %s\n" % i)
        for w in res.warnings[:20]:
            out.write("  warning: %s\n" % w)
        if len(res.warnings) > 20:
            out.write("  ... %d more warnings\n" % (len(res.warnings) - 20))
        for e in res.errors:
            out.write("  error: %s\n" % e)
        failed = failed or bool(res.errors)
    return 1 if failed else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                    help="repository root (default: parent of scripts/)")
    ap.add_argument("--gate", action="append", choices=GATES,
                    help="run only this gate (repeatable); default all")
    ap.add_argument("--write-allowlists", action="store_true",
                    help="rewrite scripts/gates/*.txt shrink-only (drop entries no longer present)")
    ap.add_argument("--allow-grow", action="store_true",
                    help="with --write-allowlists: also add new exceptions (printed as GROWING warnings; "
                         "needs justification in the PR). Never applies to the G1 list.")
    args = ap.parse_args(argv)
    if args.allow_grow and not args.write_allowlists:
        ap.error("--allow-grow requires --write-allowlists")
    gates = args.gate or list(GATES)
    return run(args.root, gates, write=args.write_allowlists, allow_grow=args.allow_grow)


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Move Lean modules and rewrite every reference to their module names.

Usage:
  python3 scripts/move_modules.py --map docs/layout-moves.json --dry-run
  python3 scripts/move_modules.py --map docs/layout-moves.json --apply [--delete-stale] [--allow-dirty]

The map is JSON: either ``{"moves": [{"old": M, "new": N, ...}, ...]}`` (extra keys
such as ``group``, ``status``, ``pr``, ``date`` are ignored) or a plain ``{old: new}``
object.  Module names are dotted (``Formalization.Ch7Rest.Marl76Defs``); file paths
``Formalization/Ch7Rest/Marl76Defs.lean`` are accepted too.

The map is cumulative.  An entry whose old file is gone and whose new file exists
counts as already applied: it is not moved again, but its references are still
rewritten and checked, so a rerun repairs a crashed run and old-path imports that
a branch added after the move landed.

What is rewritten:
  * Lean: only module names in ``import`` commands of the file header of
    ``Formalization/**/*.lean``, ``Formalization.lean`` and ``Audit.lean`` (also an
    import that follows a block comment on the same line).  No other byte of a Lean
    file changes, so no declaration name, statement or proof changes.  Path or module
    mentions inside Lean comments are reported, not edited.
  * Docs: ``Formalization/<old path>.lean`` and ``Formalization.<old module>``; a path
    tail with at least one directory (``Ch7Rest/Marl76Defs.lean``) when exactly one file
    of the tree has that tail (rewritten to the path below ``Formalization/``); and a bare
    file name (``Marl76Defs.lean``) when the move changes it and exactly one file of the
    tree has it.  Rewritten files: by default the live docs (``docs/COVERAGE.md``,
    ``docs/named-result-status.json``, ``docs/SOURCE-ISSUES.md``, ``README.md``, plus
    ``--doc`` extras) and the static-gate allowlists ``scripts/gates/*.txt``.  With
    ``--all-docs``: every text file under ``docs/``, ``site/``, ``scripts/``, ``.github/``
    and ``ci/`` and the top-level ``*.md`` files, except the paths in ``ALL_DOCS_EXCLUDE``
    (hash-pinned validation manifests, the generated graph, the move map and LAYOUT.md,
    this tool and its tests); ``--keep-history`` then also skips the review records
    ``docs/critic-*`` and ``docs/builder-*``; without it those records get only the full-path
    and module rewrites (no path tails or bare file names, which there often name a
    builder's working copy).  Markdown link text that equals the old file
    name (``[Marl76Defs.lean](../Formalization/Ch7Rest/Marl76Defs.lean)``) is renamed with
    the link.  Namespaces such as ``StatisticalRL.Ch7Rest.Marl`` or
    ``StatisticalRL.RobustRL.Ch7.LowerBound73`` never match: a dotted match needs the
    ``Formalization`` prefix, and a path match needs the ``/`` separators and ``.lean``.
  * ``--lean-comments``: the same doc rewrite inside Lean comments and docstrings of
    ``Formalization/**/*.lean``; the post-apply check then allows changes only inside
    import commands and comments.
  * Bytes are preserved exactly (line endings included) outside the rewritten names.

Refusals: moves to ``Formalization/Statements/`` and moves of the statement index
(``Statements/ChN``, ``ChNProofs``, ``QLearningProofs``), compared case-insensitively
(the site locates the statement index by path); moves of any other Statements module
unless its map entry carries ``"allow_statements_source": true``; malformed names, duplicate sources or
targets, chains, targets that already exist, case-insensitive collisions of a target
file or of any directory component with existing paths or other targets (they work on
macOS and break on Linux), and, for ``--apply``, uncommitted changes in any touched
path unless ``--allow-dirty``.

``--apply`` moves files with ``git mv`` (plain rename for untracked files), rewrites,
then checks that every touched Lean file differs only inside import commands and that
no import of an old module remains anywhere.  On any failure it rolls the working tree
back and says so.  ``--delete-stale`` then unlinks the old modules' build artifacts,
only regular files inside this project's own ``.lake/build``; it refuses when ``.lake``
or ``.lake/build`` is a symlink or resolves outside the project (this project links
read-only dependency builds; never delete through such a link).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field

IDENT = r"[A-Za-z_][A-Za-z0-9_']*"
MODULE_RE = re.compile(r"^Formalization(\." + IDENT + r")+$")
PROTECTED = "formalization.statements"
DEFAULT_DOCS = [
    "docs/COVERAGE.md",
    "docs/named-result-status.json",
    "docs/SOURCE-ISSUES.md",
    "README.md",
]
ALL_DOCS_ROOTS = ["docs", "site", "scripts", ".github", "ci"]
ALL_DOCS_TOP_EXTS = (".md",)
TEXT_EXTS = (".md", ".json", ".txt", ".py", ".js", ".css", ".html", ".yml", ".yaml", ".toml", ".sh")
SKIP_DIRS = {".git", ".lake", ".local", "_build", "__pycache__", "node_modules"}
ALL_DOCS_EXCLUDE = [
    "docs/validation/",          # validation manifests pin per-file sha256 of a past run
    "docs/graph/",               # generated by scripts/gen_nodes.py (rerun after the move)
    "docs/NEXT.md",              # generated by scripts/gen_nodes.py
    "docs/layout-moves.json",    # the move map itself (old and new names are both data)
    "docs/LAYOUT.md",            # describes the move; refresh by hand
    "scripts/move_modules.py",
    "scripts/tests/test_move_modules.py",
]
HISTORY_PREFIXES = ("docs/critic-", "docs/builder-")
INDEX_RE = re.compile(r"^formalization\.statements\.(ch\d+(proofs)?|qlearningproofs)$")
GATES_DIR = "scripts/gates"
ARTIFACT_DIRS = [".lake/build/lib/lean", ".lake/build/ir"]
ARTIFACT_EXTS = [".olean", ".ilean", ".trace", ".hash", ".olean.hash", ".ilean.hash",
                 ".c", ".c.hash", ".log.json"]
IMPORT_CMD = re.compile(r"(?m)^([ \t]*)((?:public[ \t]+)?(?:meta[ \t]+)?import)[ \t]+([^\n]*)")
FOLLOW_UP = [
    "python3 scripts/gen_nodes.py            # regenerate docs/graph/nodes.json (input hashes change)",
    "python3 scripts/static_gates.py --write-allowlists  # shrink-only; drops g2 edges a Statements move removed",
    "update docs/LAYOUT.md (sections 2 and 4 cite old paths) and layout-moves.json status/pr/date",
]


class MoveError(Exception):
    pass


def mod_to_path(mod: str) -> str:
    return mod.replace(".", "/") + ".lean"


def norm_module(name: str) -> str:
    name = name.strip()
    if name.endswith(".lean"):
        name = name[: -len(".lean")].replace("/", ".")
    return name


def read(root: str, rel: str) -> str:
    with open(os.path.join(root, rel), encoding="utf-8", newline="") as fh:
        return fh.read()


def write(root: str, rel: str, text: str) -> None:
    with open(os.path.join(root, rel), "w", encoding="utf-8", newline="") as fh:
        fh.write(text)


def load_map_entries(path: str) -> tuple[list[tuple[str, str]], set[str]]:
    """(moves, old modules whose entry has ``"allow_statements_source": true``)."""
    with open(path, encoding="utf-8") as fh:
        data = json.load(fh)
    if isinstance(data, dict) and "moves" in data:
        entries = data["moves"]
    elif isinstance(data, dict):
        entries = [{"old": o, "new": n} for o, n in data.items()]
    elif isinstance(data, list):
        entries = data
    else:
        raise MoveError("unrecognised move map format")
    moves = [(norm_module(e["old"]), norm_module(e["new"])) for e in entries]
    allow = {norm_module(e["old"]) for e in entries if e.get("allow_statements_source") is True}
    return moves, allow


def load_map(path: str) -> list[tuple[str, str]]:
    return load_map_entries(path)[0]


def scan_tree(root: str) -> tuple[set[str], set[str]]:
    """Exact-case relative paths of .lean files and of directories under Formalization/."""
    files, dirs = set(), set()
    base = os.path.join(root, "Formalization")
    for dp, dns, fs in os.walk(base):
        rel = os.path.relpath(dp, root).replace(os.sep, "/")
        dirs.add(rel)
        for f in fs:
            if f.endswith(".lean"):
                files.add(f"{rel}/{f}")
    return files, dirs


def dir_prefixes(path: str) -> list[str]:
    parts = path.split("/")[:-1]
    return ["/".join(parts[: i + 1]) for i in range(len(parts))]


def is_statements(m: str) -> bool:
    low = m.lower()
    return low == PROTECTED or low.startswith(PROTECTED + ".")


def validate(moves: list[tuple[str, str]], root: str,
             allow_statements: set[str] | frozenset = frozenset()) -> tuple[list[tuple[str, str]], list[tuple[str, str]]]:
    """Return (pending, already_applied); raise MoveError on any refusal."""
    errors: list[str] = []
    olds: dict[str, int] = {}
    news: dict[str, int] = {}
    for old, new in moves:
        for m in (old, new):
            if not MODULE_RE.match(m):
                errors.append(f"malformed module name: {m!r}")
        if is_statements(new):
            errors.append(f"refusing to move into Statements: {old} -> {new}")
        if is_statements(old):
            if INDEX_RE.match(old.lower()):
                errors.append(f"refusing to move Statements index module: {old} -> {new}")
            elif old not in allow_statements:
                errors.append(f"refusing to move Statements module without allow_statements_source: {old} -> {new}")
        if old == new:
            errors.append(f"identity move: {old}")
        olds[old] = olds.get(old, 0) + 1
        news[new] = news.get(new, 0) + 1
    errors += [f"duplicate source: {m}" for m, c in olds.items() if c > 1]
    errors += [f"duplicate target: {m}" for m, c in news.items() if c > 1]
    if errors:
        raise MoveError("\n".join(errors))

    files, dirs = scan_tree(root)
    pending, applied = [], []
    for old, new in moves:
        o_ex = mod_to_path(old) in files
        n_ex = mod_to_path(new) in files
        if o_ex and not n_ex:
            pending.append((old, new))
        elif n_ex and not o_ex:
            applied.append((old, new))
        elif o_ex and n_ex:
            errors.append(f"both source and target exist: {old} -> {new}")
        else:
            errors.append(f"neither source nor target exists: {old} -> {new}")
    pend_old = {o for o, _ in pending}
    for _, new in pending:
        if new in pend_old:
            errors.append(f"chained move (target is also a pending source): {new}")

    # case-insensitive collisions: files, and every directory component
    files_low = {f.lower(): f for f in files}
    dirs_low = {d.lower(): d for d in dirs}
    seen_files: dict[str, str] = {}
    for old, new in pending + applied:
        for d in dir_prefixes(mod_to_path(new)):
            if d.lower() in dirs_low and dirs_low[d.lower()] != d:
                errors.append(f"target directory {d} differs only in case from existing {dirs_low[d.lower()]}: {new}")
            dirs_low.setdefault(d.lower(), d)  # later targets must agree with earlier ones
    for old, new in pending:
        key = mod_to_path(new).lower()
        if key in files_low and files_low[key] != mod_to_path(old):
            errors.append(f"target collides (case-insensitively) with existing {files_low[key]}: {new}")
        if key in seen_files:
            errors.append(f"targets collide case-insensitively: {seen_files[key]} / {new}")
        seen_files[key] = new
    if errors:
        raise MoveError("\n".join(sorted(set(errors), key=errors.index)))
    return pending, applied


# ---------------------------------------------------------------- Lean lexing

def comment_spans(text: str) -> list[tuple[int, int]]:
    """(start, end) offsets of Lean comments (line and nested block); string and char
    literals are skipped."""
    spans: list[tuple[int, int]] = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "'" and i + 2 < n and text[i + 2] == "'" and text[i + 1] != "\\":
            i += 3  # char literal such as '"'
        elif c == "'" and i + 3 < n and text[i + 1] == "\\" and text[i + 3] == "'":
            i += 4  # escaped char literal such as '\n'
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            spans.append((i, j))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            spans.append((i, j))
            i = j
        else:
            i += 1
    return spans


def mask_comments(text: str) -> str:
    """Replace Lean comments (line and nested block) by spaces, keeping newlines and
    offsets; string literals are skipped (left intact)."""
    out = list(text)
    for a, b in comment_spans(text):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "
    return "".join(out)


def code_only(text: str) -> str:
    """Text with header import module tokens and comment contents removed."""
    text = without_imports(text)
    for a, b in reversed(comment_spans(text)):
        text = text[:a] + "\x00" + text[b:]
    return text


def rewrite_lean_comments(text: str, mapping: dict[str, str], regs) -> tuple[str, list[tuple[int, str, str]]]:
    new = text
    for a, b in reversed(comment_spans(text)):
        seg, _ = rewrite_doc(new[a:b], mapping, regs)
        new = new[:a] + seg + new[b:]
    if new == text:
        return text, []
    x, y = text.split("\n"), new.split("\n")
    return new, [(i + 1, p.rstrip("\r"), q.rstrip("\r")) for i, (p, q) in enumerate(zip(x, y)) if p != q]


def import_spans(text: str) -> tuple[list[tuple[int, int, str]], int, list[int]]:
    """Module tokens of header import commands as (start, end, token), the header end
    offset, and offsets of import commands found after the header (Lean would reject
    those; they make the file unparsable for this tool)."""
    masked = mask_comments(text)
    spans: list[tuple[int, int, str]] = []
    pos = 0
    header_end = len(masked)
    for line in masked.splitlines(keepends=True):
        st = line.strip()
        m = IMPORT_CMD.match(line)
        if not st or st == "prelude" or st == "module":
            pos += len(line)
            continue
        if m:
            body_start = pos + m.start(3)
            for t in re.finditer(r"\S+", m.group(3)):
                spans.append((body_start + t.start(), body_start + t.end(), t.group()))
            pos += len(line)
            continue
        header_end = pos
        break
    late = [pos_m.start() for pos_m in IMPORT_CMD.finditer(masked, header_end)]
    return spans, header_end, late


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def line_at(text: str, offset: int) -> str:
    a = text.rfind("\n", 0, offset) + 1
    b = text.find("\n", offset)
    return text[a: len(text) if b < 0 else b].rstrip("\r")


def rewrite_imports(text: str, mapping: dict[str, str]) -> tuple[str, list[tuple[int, str, str]]]:
    spans, _, _ = import_spans(text)
    hits = [(a, b, mapping[t]) for a, b, t in spans if t in mapping]
    if not hits:
        return text, []
    new = text
    for a, b, rep in reversed(hits):
        new = new[:a] + rep + new[b:]
    changes, done = [], set()
    for a, _, _ in hits:
        ln = line_of(text, a)
        if ln not in done:
            done.add(ln)
            changes.append((ln, line_at(text, a), new.split("\n")[ln - 1].rstrip("\r")))
    return new, changes


def without_imports(text: str) -> str:
    """Text with header import module tokens removed (for the content-unchanged check)."""
    spans, _, _ = import_spans(text)
    for a, b, _ in reversed(spans):
        text = text[:a] + text[b:]
    return text


# ---------------------------------------------------------------- docs

def tail_maps(mapping: dict[str, str], universe: set[str]) -> tuple[dict[str, str], dict[str, str]]:
    """Unambiguous short forms of old paths -> replacement (path below ``Formalization/``).

    ``tails``: path tails with at least one directory (``Ch7Rest/Marl76Defs.lean``) that
    exactly one file of ``universe`` (all .lean paths before the move) has.  ``bases``: bare
    file names that the move changes and that exactly one file of ``universe`` has."""
    count: dict[str, int] = {}
    for f in universe:
        parts = f.split("/")
        for k in range(1, len(parts)):  # tails below Formalization/, down to the bare name
            t = "/".join(parts[k:])
            count[t] = count.get(t, 0) + 1
    tails, bases = {}, {}
    for o, n in mapping.items():
        op, np_ = mod_to_path(o), mod_to_path(n)
        rel_new = np_.split("/", 1)[1]
        parts = op.split("/")
        for k in range(1, len(parts) - 1):
            t = "/".join(parts[k:])
            if count.get(t, 0) == 1 and not np_.endswith("/" + t):
                tails[t] = rel_new
        base = parts[-1]
        if count.get(base, 0) == 1 and base != np_.rsplit("/", 1)[-1]:
            bases[base] = rel_new
    return tails, bases


def doc_regexes(mapping: dict[str, str], universe: set[str] | None = None):
    if not mapping:
        return None
    alts_path = sorted((re.escape(mod_to_path(o)) for o in mapping), key=len, reverse=True)
    alts_mod = sorted((re.escape(o) for o in mapping), key=len, reverse=True)
    path_re = re.compile(r"(?<![A-Za-z0-9_'])(" + "|".join(alts_path) + r")(?![A-Za-z0-9_'])")
    mod_re = re.compile(r"(?<![A-Za-z0-9_'.])(" + "|".join(alts_mod) + r")(?![A-Za-z0-9_'])(?!\.[A-Za-z_])")
    link_re = re.compile(r"\[([^\]\n]+)\]\(([^)\s]*?)(" + "|".join(alts_path) + r")([^)\s]*)\)")
    path_map = {mod_to_path(o): mod_to_path(n) for o, n in mapping.items()}
    if universe is None:
        universe = set(path_map)
    tails, bases = tail_maps(mapping, set(universe) | set(path_map))
    short = {**bases, **tails}
    short_re = None
    if short:
        alts = sorted((re.escape(t) for t in short), key=len, reverse=True)
        short_re = re.compile(r"(?<![A-Za-z0-9_'./\-])(" + "|".join(alts) + r")(?![A-Za-z0-9_'])")
    return path_re, mod_re, link_re, path_map, short_re, short


def full_only(regs):
    """``regs`` without the short forms (path tails, bare file names)."""
    return None if regs is None else regs[:4] + (None, {})


def regs_for(rel: str, regs):
    """Review records get only full-path and module rewrites: their bare file names often
    name a builder's working copy, not the repository module."""
    return full_only(regs) if rel.startswith(HISTORY_PREFIXES) else regs


def rewrite_doc(text: str, mapping: dict[str, str], regs) -> tuple[str, list[tuple[int, str, str]]]:
    if regs is None:
        return text, []
    path_re, mod_re, link_re, path_map, short_re, short = regs

    def relabel(m):
        label, old = m.group(1), m.group(3)
        tick = label.startswith("`") and label.endswith("`") and len(label) > 1
        core = label[1:-1] if tick else label
        if core == old or old.endswith("/" + core):
            k = core.count("/") + 1
            core = "/".join(path_map[old].split("/")[-k:])
            label = f"`{core}`" if tick else core
        return f"[{label}]({m.group(2)}{old}{m.group(4)})"

    new = link_re.sub(relabel, text)
    new = path_re.sub(lambda m: path_map[m.group(1)], new)
    new = mod_re.sub(lambda m: mapping[m.group(1)], new)
    if short_re is not None:
        new = short_re.sub(lambda m: short[m.group(1)], new)
    if new == text:
        return text, []
    a, b = text.split("\n"), new.split("\n")
    changes = [(i + 1, x.rstrip("\r"), y.rstrip("\r")) for i, (x, y) in enumerate(zip(a, b)) if x != y]
    return new, changes


def lean_files(root: str) -> list[str]:
    out = [t for t in ("Formalization.lean", "Audit.lean") if os.path.isfile(os.path.join(root, t))]
    for dp, dns, fs in os.walk(os.path.join(root, "Formalization")):
        dns.sort()
        for f in sorted(fs):
            if f.endswith(".lean"):
                out.append(os.path.relpath(os.path.join(dp, f), root).replace(os.sep, "/"))
    return out


def excluded(rel: str, keep_history: bool) -> bool:
    if any(rel == e or (e.endswith("/") and rel.startswith(e)) for e in ALL_DOCS_EXCLUDE):
        return True
    return keep_history and rel.startswith(HISTORY_PREFIXES)


def all_doc_files(root: str, keep_history: bool) -> list[str]:
    out = []
    for f in sorted(os.listdir(root)):
        if f.endswith(ALL_DOCS_TOP_EXTS) and os.path.isfile(os.path.join(root, f)):
            out.append(f)
    for top in ALL_DOCS_ROOTS:
        for dp, dns, fs in os.walk(os.path.join(root, top)):
            dns[:] = sorted(d for d in dns if d not in SKIP_DIRS)
            for f in sorted(fs):
                if f.endswith(TEXT_EXTS):
                    rel = os.path.relpath(os.path.join(dp, f), root).replace(os.sep, "/")
                    if not excluded(rel, keep_history):
                        out.append(rel)
    return out


def doc_files(root: str, extra: list[str], all_docs: bool = False, keep_history: bool = False) -> list[str]:
    out = [d for d in DEFAULT_DOCS + list(extra) if os.path.isfile(os.path.join(root, d))]
    gd = os.path.join(root, GATES_DIR)
    if os.path.isdir(gd):
        out += sorted(f"{GATES_DIR}/{f}" for f in os.listdir(gd) if f.endswith(".txt"))
    if all_docs:
        out += [f for f in all_doc_files(root, keep_history) if f not in out]
    return out


# ---------------------------------------------------------------- build artifacts

def build_dir_problem(root: str) -> str | None:
    """Why deleting under .lake/build would be unsafe, or None."""
    lake = os.path.join(root, ".lake")
    build = os.path.join(lake, "build")
    if not os.path.lexists(build):
        return None
    if os.path.islink(lake):
        return ".lake is a symlink"
    if os.path.islink(build):
        return ".lake/build is a symlink"
    real_root = os.path.realpath(root)
    real_build = os.path.realpath(build)
    if not real_build.startswith(real_root + os.sep):
        return f".lake/build resolves outside the project ({real_build})"
    return None


def stale_artifacts(root: str, olds: list[str]) -> tuple[list[str], list[str]]:
    """(deletable regular files, refused entries with reasons)."""
    ok, refused = [], []
    problem = build_dir_problem(root)
    real_build = os.path.realpath(os.path.join(root, ".lake", "build"))
    for old in olds:
        stem = old.replace(".", "/")
        for d in ARTIFACT_DIRS:
            for ext in ARTIFACT_EXTS:
                rel = f"{d}/{stem}{ext}"
                p = os.path.join(root, rel)
                if not os.path.lexists(p):
                    continue
                if problem:
                    refused.append(f"{rel} ({problem})")
                elif os.path.islink(p) or not os.path.isfile(p):
                    refused.append(f"{rel} (not a regular file)")
                elif not os.path.realpath(p).startswith(real_build + os.sep):
                    refused.append(f"{rel} (resolves outside .lake/build)")
                else:
                    ok.append(rel)
    return ok, refused


# ---------------------------------------------------------------- git

def in_git(root: str) -> bool:
    r = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=root, capture_output=True, text=True)
    return r.returncode == 0 and os.path.realpath(r.stdout.strip()) == os.path.realpath(root)


def is_tracked(root: str, rel: str) -> bool:
    r = subprocess.run(["git", "ls-files", "--error-unmatch", "--", rel], cwd=root,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return r.returncode == 0


def dirty_paths(root: str, paths: list[str]) -> list[str]:
    if not paths or not in_git(root):
        return []
    out = []
    for i in range(0, len(paths), 200):
        r = subprocess.run(["git", "status", "--porcelain", "--untracked-files=all", "--"] + paths[i:i + 200],
                           cwd=root, capture_output=True, text=True, check=True)
        out += [l for l in r.stdout.splitlines() if l.strip()]
    return out


# ---------------------------------------------------------------- planning

@dataclass
class Plan:
    pending: list = field(default_factory=list)
    applied: list = field(default_factory=list)
    lean_changes: dict = field(default_factory=dict)   # current path -> [(line, old, new)]
    doc_changes: dict = field(default_factory=dict)
    lean_mentions: list = field(default_factory=list)
    comment_changes: dict = field(default_factory=dict)  # --lean-comments: current path -> changes
    short_leftovers: list = field(default_factory=list)   # bare module stems / globs not rewritten
    unparsable: list = field(default_factory=list)     # (path, line) import after header
    leftovers: list = field(default_factory=list)
    remaining: dict = field(default_factory=dict)
    stale: list = field(default_factory=list)
    stale_refused: list = field(default_factory=list)


def universe_of(root: str, mapping: dict[str, str]) -> set[str]:
    """All .lean paths before and after the move (the same set on a rerun)."""
    return scan_tree(root)[0] | {mod_to_path(o) for o in mapping} | {mod_to_path(n) for n in mapping.values()}


def stem_re(mapping: dict[str, str]):
    """Bare old module stems whose file name changes (``Marl76Defs``) and glob mentions."""
    stems = sorted({mod_to_path(o).rsplit("/", 1)[1][:-5] for o, n in mapping.items()
                    if mod_to_path(o).rsplit("/", 1)[1] != mod_to_path(n).rsplit("/", 1)[1]}, key=len, reverse=True)
    if not stems:
        return None
    return re.compile(r"(?<![A-Za-z0-9_'])(" + "|".join(map(re.escape, stems)) + r")(?![A-Za-z0-9_'])")


def build_plan(root: str, map_path: str, extra_docs: list[str], all_docs: bool = False,
               keep_history: bool = False, lean_comments: bool = False) -> tuple[Plan, dict[str, str]]:
    moves, allow = load_map_entries(map_path)
    pending, applied = validate(moves, root, allow)
    mapping = dict(pending + applied)  # applied entries are rewritten too (idempotent)
    plan = Plan(pending=pending, applied=applied)
    regs = doc_regexes(mapping, universe_of(root, mapping))
    for rel in lean_files(root):
        text = read(root, rel)
        new, ch = rewrite_imports(text, mapping)
        if ch:
            plan.lean_changes[rel] = ch
        _, _, late = import_spans(text)
        plan.unparsable += [(rel, line_of(text, o)) for o in late]
        import_lines = {c[0] for c in ch}
        if mapping and lean_comments:
            _, cch = rewrite_lean_comments(new, mapping, regs)
            if cch:
                plan.comment_changes[rel] = cch
        elif mapping:
            _, mentions = rewrite_doc(text, mapping, regs)
            plan.lean_mentions += [(rel, ln, old.strip()) for ln, old, _ in mentions if ln not in import_lines]
    docs = doc_files(root, extra_docs, all_docs, keep_history)
    sre = stem_re(mapping)
    for rel in docs:
        new, ch = rewrite_doc(read(root, rel), mapping, regs_for(rel, regs))
        if ch:
            plan.doc_changes[rel] = ch
        if sre is not None:
            for i, line in enumerate(new.split("\n")):
                if sre.search(line):
                    plan.short_leftovers.append((rel, i + 1, line.strip()))
    moved_paths = {mod_to_path(o) for o, _ in pending}
    for d in sorted({os.path.dirname(p) for p in moved_paths}):
        rest = sorted(f"{d}/{f}" for f in os.listdir(os.path.join(root, d))
                      if f.endswith(".lean") and f"{d}/{f}" not in moved_paths)
        plan.remaining[d] = rest
    emptied = [d for d, rest in plan.remaining.items() if not rest]
    emptied += sorted({os.path.dirname(mod_to_path(o)) for o, _ in applied}
                      - {os.path.dirname(f) for f in scan_tree(root)[0]})
    if emptied:
        pats = []
        for d in sorted(set(emptied)):
            pats.append(re.escape(d + "/"))
            pats.append(r"(?<![A-Za-z0-9_'.])" + re.escape(d.replace("/", ".") + "."))
        left_re = re.compile("|".join(pats))
        for rel in docs:
            new, _ = rewrite_doc(read(root, rel), mapping, regs_for(rel, regs))
            for i, line in enumerate(new.split("\n")):
                if left_re.search(line):
                    plan.leftovers.append((rel, i + 1, line.strip()))
    plan.stale, plan.stale_refused = stale_artifacts(root, list(mapping))
    return plan, mapping


def short(s: str, n: int = 160) -> str:
    return s if len(s) <= n else s[: n - 3] + "..."


def report(plan: Plan, mapping: dict[str, str], out) -> None:
    w = lambda s="": print(s, file=out)  # noqa: E731
    n_imp = sum(len(v) for v in plan.lean_changes.values())
    n_doc = sum(len(v) for v in plan.doc_changes.values())
    w("== move_modules summary")
    w(f"pending moves: {len(plan.pending)}; already applied (skipped): {len(plan.applied)}")
    w(f"Lean import lines rewritten: {n_imp} in {len(plan.lean_changes)} files")
    w(f"doc/allowlist lines rewritten: {n_doc} in {len(plan.doc_changes)} files")
    w(f"Lean non-import mentions left as is (comments/docstrings): {len(plan.lean_mentions)}")
    w(f"Lean comment/docstring lines rewritten (--lean-comments): "
      f"{sum(len(v) for v in plan.comment_changes.values())} in {len(plan.comment_changes)} files")
    w(f"doc lines still naming an old module stem (prose, globs; not rewritten): {len(plan.short_leftovers)}")
    w(f"unresolved mentions of emptied directories in docs: {len(plan.leftovers)}")
    w(f"stale build artifacts of moved modules: {len(plan.stale)} deletable, {len(plan.stale_refused)} refused")
    if plan.unparsable:
        w(f"ERROR: {len(plan.unparsable)} import commands after the file header (apply will refuse)")
    w()
    w("== moves")
    for old, new in plan.pending:
        w(f"  {mod_to_path(old)} -> {mod_to_path(new)}")
    for old, new in plan.applied:
        w(f"  (already applied) {old} -> {new}")
    w()
    w("== Lean import rewrites")
    for rel in sorted(plan.lean_changes):
        mod = rel[:-5].replace("/", ".")
        dest = mod_to_path(mapping[mod]) if mod in dict(plan.pending) else rel
        w(f"-- {rel}" + (f"  (file moves to {dest})" if dest != rel else ""))
        for ln, old, new in plan.lean_changes[rel]:
            w(f"  {ln}: - {old.strip()}")
            w(f"  {ln}: + {new.strip()}")
    w()
    w("== doc and allowlist rewrites")
    for rel in sorted(plan.doc_changes):
        w(f"-- {rel}")
        for ln, old, new in plan.doc_changes[rel]:
            w(f"  {ln}: - {short(old.strip())}")
            w(f"  {ln}: + {short(new.strip())}")
    w()
    w("== Lean comment/docstring rewrites (--lean-comments)")
    for rel in sorted(plan.comment_changes):
        w(f"-- {rel}")
        for ln, old, new in plan.comment_changes[rel]:
            w(f"  {ln}: - {short(old.strip())}")
            w(f"  {ln}: + {short(new.strip())}")
    w()
    w("== source directories: files not covered by the map (stay in place)")
    for d, rest in sorted(plan.remaining.items()):
        w(f"  {d}: {len(rest)} remaining" + ("" if rest else " (directory emptied)"))
        for r in rest[:10]:
            w(f"    {r}")
        if len(rest) > 10:
            w(f"    ... (+{len(rest) - 10} more)")
    w()
    w("== manual follow-up: emptied-directory mentions not rewritten (globs, prose)")
    for rel, ln, txt in plan.leftovers:
        w(f"  {rel}:{ln}: {short(txt)}")
    w()
    w("== manual follow-up: old module stems in docs (prose, globs, namespaces-like text; not rewritten)")
    for rel, ln, txt in plan.short_leftovers:
        w(f"  {rel}:{ln}: {short(txt)}")
    w()
    w("== Lean comment/docstring mentions of moved modules (not edited without --lean-comments)")
    for rel, ln, txt in plan.lean_mentions:
        w(f"  {rel}:{ln}: {short(txt)}")
    if plan.unparsable:
        w()
        w("== import commands after the header (fix by hand first)")
        for rel, ln in plan.unparsable:
            w(f"  {rel}:{ln}")
    w()
    w("== stale build artifacts (delete before a local check; --apply --delete-stale does it)")
    for p in plan.stale:
        w(f"  {p}")
    for p in plan.stale_refused:
        w(f"  REFUSED {p}")
    w()
    w("== required follow-up in the same change")
    for s in FOLLOW_UP:
        w(f"  {s}")


# ---------------------------------------------------------------- apply

def apply(root: str, plan: Plan, mapping: dict[str, str], delete_stale: bool, allow_dirty: bool, out,
          lean_comments: bool = False) -> None:
    pend = dict(plan.pending)
    if plan.unparsable:
        raise MoveError("import commands after the file header: " +
                        ", ".join(f"{r}:{l}" for r, l in plan.unparsable))
    if delete_stale and plan.stale_refused:
        raise MoveError("refusing --delete-stale:\n  " + "\n  ".join(plan.stale_refused))
    touched = sorted(set(plan.lean_changes) | set(plan.doc_changes) | set(plan.comment_changes)
                     | {mod_to_path(o) for o in pend})
    if not allow_dirty:
        dirty = dirty_paths(root, touched)
        if dirty:
            raise MoveError("uncommitted changes in touched paths (commit/stash them or pass --allow-dirty):\n  "
                            + "\n  ".join(dirty))

    def final(rel: str) -> str:
        mod = rel[:-5].replace("/", ".") if rel.endswith(".lean") else None
        return mod_to_path(pend[mod]) if mod in pend else rel

    before = {rel: read(root, rel) for rel in touched}
    use_git = in_git(root)
    done_moves: list[tuple[str, str, bool]] = []
    created_dirs: list[str] = []
    written: list[str] = []
    try:
        for old, new in plan.pending:
            src, dst = mod_to_path(old), mod_to_path(new)
            d = os.path.dirname(dst)
            missing = []
            while d and not os.path.isdir(os.path.join(root, d)):
                missing.append(d)
                d = os.path.dirname(d)
            for d in reversed(missing):
                os.mkdir(os.path.join(root, d))
                created_dirs.append(d)
            tracked = use_git and is_tracked(root, src)
            if tracked:
                subprocess.run(["git", "mv", "--", src, dst], cwd=root, check=True)
            else:
                os.rename(os.path.join(root, src), os.path.join(root, dst))
            done_moves.append((src, dst, tracked))
        regs = doc_regexes(mapping, universe_of(root, mapping))
        for rel in sorted(set(plan.lean_changes) | set(plan.comment_changes)):
            new, _ = rewrite_imports(read(root, final(rel)), mapping)
            if lean_comments:
                new, _ = rewrite_lean_comments(new, mapping, regs)
            write(root, final(rel), new)
            written.append(final(rel))
        for rel in plan.doc_changes:
            new, _ = rewrite_doc(read(root, rel), mapping, regs_for(rel, regs))
            if rel.endswith(".json"):
                json.loads(new)
            write(root, rel, new)
            written.append(rel)
        problems = []
        for rel, old_text in before.items():
            new_text = read(root, final(rel))
            strip = code_only if lean_comments else without_imports
            if rel.endswith(".lean") and strip(old_text) != strip(new_text):
                where = "import commands and comments" if lean_comments else "import commands"
                problems.append(f"content outside {where} changed: {rel}")
        olds = set(mapping)
        for rel in lean_files(root):
            text = read(root, rel)
            masked = mask_comments(text)
            for m in IMPORT_CMD.finditer(masked):
                if any(t in olds for t in m.group(3).split()):
                    problems.append(f"import of moved module remains: {rel}:{line_of(text, m.start())}")
        if problems:
            raise MoveError("post-apply check failed:\n  " + "\n  ".join(problems))
    except Exception as exc:
        rollback(root, before, final, done_moves, created_dirs, out)
        if isinstance(exc, MoveError):
            raise MoveError(f"{exc}\nthe working tree was rolled back; nothing was moved") from exc
        raise MoveError(f"unexpected failure ({exc!r}); the working tree was rolled back") from exc
    # remove source directories left empty
    for d in sorted({os.path.dirname(s) for s, _, _ in done_moves}, key=len, reverse=True):
        full = os.path.join(root, d)
        while os.path.isdir(full) and not os.listdir(full) and \
                os.path.realpath(full) != os.path.realpath(os.path.join(root, "Formalization")):
            os.rmdir(full)
            full = os.path.dirname(full)
    if delete_stale:
        for p in plan.stale:
            os.unlink(os.path.join(root, p))


def rollback(root, before, final, done_moves, created_dirs, out) -> None:
    errs = []
    for rel, text in before.items():
        try:
            if os.path.exists(os.path.join(root, final(rel))):
                write(root, final(rel), text)
        except OSError as e:
            errs.append(str(e))
    for src, dst, tracked in reversed(done_moves):
        try:
            if tracked:
                subprocess.run(["git", "mv", "--", dst, src], cwd=root, check=True)
            else:
                os.rename(os.path.join(root, dst), os.path.join(root, src))
        except Exception as e:  # noqa: BLE001
            errs.append(f"{dst} -> {src}: {e}")
    for d in reversed(created_dirs):
        full = os.path.join(root, d)
        if os.path.isdir(full) and not os.listdir(full):
            os.rmdir(full)
    if errs:
        print("ROLLBACK INCOMPLETE; recover with `git status`, `git restore --staged --worktree -- "
              "Formalization Formalization.lean Audit.lean docs scripts/gates` and `git clean -n Formalization`:\n  "
              + "\n  ".join(errs), file=out)


def main(argv: list[str] | None = None, out=sys.stdout) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--map", required=True, help="JSON move map")
    ap.add_argument("--root", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--dry-run", action="store_true", help="print every change, write nothing")
    mode.add_argument("--apply", action="store_true", help="move files and rewrite references")
    ap.add_argument("--doc", action="append", default=[], help="extra live doc to rewrite (repeatable)")
    ap.add_argument("--all-docs", action="store_true",
                    help="rewrite every text file under docs/, site/, scripts/, .github/, ci/ and top-level *.md "
                         "(except ALL_DOCS_EXCLUDE)")
    ap.add_argument("--keep-history", action="store_true",
                    help="with --all-docs: do not rewrite review records docs/critic-*, docs/builder-*")
    ap.add_argument("--lean-comments", action="store_true",
                    help="also rewrite path and module mentions inside Lean comments and docstrings")
    ap.add_argument("--delete-stale", action="store_true",
                    help="with --apply: unlink moved modules' artifacts in this project's own .lake/build")
    ap.add_argument("--allow-dirty", action="store_true",
                    help="with --apply: proceed although touched paths have uncommitted changes")
    args = ap.parse_args(argv)
    if (args.delete_stale or args.allow_dirty) and not args.apply:
        ap.error("--delete-stale and --allow-dirty require --apply")
    if args.keep_history and not args.all_docs:
        ap.error("--keep-history requires --all-docs")
    root = os.path.abspath(args.root)
    map_path = args.map
    if not os.path.isabs(map_path) and not os.path.isfile(map_path):
        map_path = os.path.join(root, map_path)
    try:
        plan, mapping = build_plan(root, map_path, args.doc, args.all_docs, args.keep_history, args.lean_comments)
        report(plan, mapping, out)
        if args.dry_run:
            touched = sorted(set(plan.lean_changes) | set(plan.doc_changes) | set(plan.comment_changes)
                             | {mod_to_path(o) for o, _ in plan.pending})
            dirty = dirty_paths(root, touched)
            if dirty:
                print(f"\nWARNING: {len(dirty)} touched paths have uncommitted changes; --apply will refuse "
                      "without --allow-dirty:\n  " + "\n  ".join(dirty), file=out)
        if args.apply:
            apply(root, plan, mapping, args.delete_stale, args.allow_dirty, out, args.lean_comments)
            print(f"\napplied {len(plan.pending)} moves; rewrote references for {len(mapping)} entries", file=out)
    except MoveError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Generate the source-result node graph and the "what next" list.

    python3 scripts/gen_nodes.py            # write docs/graph/nodes.json and docs/NEXT.md
    python3 scripts/gen_nodes.py --check    # fail if either file is stale (no writes)
    python3 scripts/gen_nodes.py --summary  # print counts only (no writes)

Both outputs are derived purely from committed project files and are never
edited by hand:

  docs/source-inventory.json        nodes, numbers, .tex ranges, cross-references
  docs/named-result-status.json     the reviewed named-result ledger
  docs/COVERAGE.md                  the reviewed coverage ledger (partial / refuted notes,
                                    prose claims)
  docs/SOURCE-ISSUES.md             valid C-ids
  Formalization/Statements/ChN.lean, ChNProofs.lean
                                    statement-index entries and their `_holds` wrappers

Status rules (also shown in words on the site's Status and Graph pages):

* A numbered theorem, lemma or claim ("named" node) is proved only if the named-result
  ledger has a record for it.  Its statement status is `printed`, `corrected` or
  `restricted` by the same rule the reader uses (`site/reader/lean.py: classify`).
* A remark or displayed claim ("prose" node) is proved only if it has both a
  statement-index entry and a COVERAGE row (COVERAGE is its reviewed ledger).
* `refuted`: nothing is proved for the node and one of its COVERAGE rows cites a Lean
  refutation of the printed statement by name (backticked `not_..._printed...`, the
  project convention; G4 in static_gates.py checks cited names resolve).  A node that
  is proved in some form is never marked refuted; its `refutations_cited` field lists
  any such names as data only (also names of the form `not_..._printed` in a ledger record).
  `partial`: a COVERAGE row whose bold lead starts with "Partial" or proves only part of the
  item ("First two sentences proved"), or a statement entry without the reviewed record it needs.
* Source-issue ids are read from ledger scopes and docstrings as `Cnn` (not `C1 = 2`), and from
  COVERAGE rows only as links (`SOURCE-ISSUES.md#Cnn`, `[Cnn]`), since rows use constants C1, C2.
* Fail-closed: if a proved node's COVERAGE headline says "Partial", or says "refuted"
  without saying anything is proved, the headline wins and a warning is emitted.
* `open`: a named node with nothing recorded.  `prose-claim`: a prose node with no
  statement entry (it may have a COVERAGE note).
* A joint statement entry (one Prop for several displays) is attached to every cited
  label whose range lies inside the entry's first cited range.
* `printed_with_cited_printed`: statement `printed`, proof `proved`, and every node reachable
  through `uses` is also proved as printed.  `uses` edges are candidates read from the TeX
  cross-references (`\\ref`, `\\eqref`, ...) inside the result and its proof; they are
  NOT reviewed (`"reviewed": false`), so this flag is not a reviewed proof-dependency check:
  it says nothing about whether the cited results are what the proof actually needs.

Python 3.9+, standard library only, read-only on everything except the two outputs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NODES_PATH = "docs/graph/nodes.json"
NEXT_PATH = "docs/NEXT.md"
SCHEMA_VERSION = 1

NAMED_KINDS = ("theorem", "lemma", "claim")
PROSE_KINDS = ("remark",)            # always nodes, even with nothing recorded
CONTEXT_KINDS = ("definition", "assumption", "algorithm")  # edge targets only, never "proved"
STATEMENT_STATUSES = ("printed", "corrected", "restricted", "refuted", "partial", "open", "prose-claim")
PROOF_STATUSES = ("proved", "refuted", "open")

# Same regexes as site/reader/lean.py (scripts/tests/test_gen_nodes.py asserts they agree).
RANGE_RE = re.compile(r"`?((?:[\w-]+/)*[\w-]+\.tex):(\d+)(?:[–-](\d+))?`?")
LABEL_RE = re.compile(r"`([A-Za-z][\w-]*:[^`\s]+)`")
DECL_RE = re.compile(r"/--(?P<doc>.*?)-/\s*\n(?P<decl>(?:noncomputable\s+)?def\s+(?P<name>[\w']+)\b.*?)"
                     r"(?=\n\s*\n|\n/--|\nend\b|\Z)", re.S)
HOLDS_RE = re.compile(r"^(?:noncomputable\s+)?theorem\s+([\w']+)_holds\b", re.M)
QUALIFIED_RE = re.compile(r"\b(?:StatisticalRL|[A-Z][\w']*)(?:\.[\w']+)+")
CID_RE = re.compile(r"\bC(\d+)\b(?!\s*[=≤≥<>])")  # not constants such as "C1 = 2"
# In the coverage ledger, prose also uses constants named C1, C2 ("C1 log(N/(1−γ))"), so an issue
# id is read there only from a link to SOURCE-ISSUES.md or a bracketed [Cnn] link text.
CID_LINK_RE = re.compile(r"SOURCE-ISSUES\.md#C(\d+)\b|\[C(\d+)\]")


def coverage_issue_ids(text: str) -> list:
    return [a or b for a, b in CID_LINK_RE.findall(text)]
# A Lean refutation of a printed statement, by the project's naming convention
# (`not_thm7_11_printed`, `not_Eq_PAC_from_regret_conversion_printed`, ...), cited in backticks.
REFUTATION_RE = re.compile(r"`(?:[\w.']*\.)?(not_[\w']*printed[\w']*)`")
NUMBERED_REF_RE = re.compile(r"\b(Theorem|Lemma|Claim|Remark)s?\s+(\d+\.\d+)((?:\s*(?:,|and)\s*\d+\.\d+)*)")
PROOF_TITLE_RE = re.compile(r"(?:proof|analysis)\b[^$]*?\\(?:ref|eqref|Cref|cref)\{([^}]+)\}", re.I)


def namespace_at(text: str, upto: int) -> str:
    stack = []
    for line in text.splitlines()[:upto - 1]:
        m = re.match(r"namespace\s+([\w.]+)", line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"end\s+([\w.]+)\s*$", line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
    return ".".join(stack)


def split_md_row(line: str) -> list:
    """Cells of a Markdown table row. `|` inside backticks, or escaped as `\\|`, is literal."""
    cells, cur, tick = [], [], False
    for ch in line.strip().strip("|"):
        if ch == "`":
            tick = not tick
        if ch == "|" and cur and cur[-1] == "\\":
            cur[-1] = "|"
        elif ch == "|" and not tick:
            cells.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    cells.append("".join(cur).strip())
    return cells


def partial_lead(lead: str) -> bool:
    """A coverage headline that proves only part of the item ("Partial: ...", "First two sentences
    proved"). Proving part of a claim is partial, not a restricted case."""
    lead = lead.lower()
    return lead.startswith("partial") or bool(re.search(r"\bfirst\b|\bpart\b|\bsentences?\b", lead))


def coverage_partial(name: str, coverage_rows: list) -> bool:
    """True when a row naming the entry as its subject has a partial headline."""
    for row in coverage_rows:
        rest = re.sub(r"^\s*\*\*.+?\*\*", "", row["scope"], count=1)
        paren = re.match(r"\s*\(([^)]*)\)", rest)
        first = re.search(r"`([^`]+)`", rest)
        subjects = re.findall(r"`([^`]+)`", paren.group(1)) if paren else ([first.group(1)] if first else [])
        if name in [x.rsplit(".", 1)[-1] for x in subjects] and partial_lead(row["lead"]):
            return True
    return False


def coverage_variant(name: str, coverage_rows: list) -> str | None:
    """Variant that the coverage ledger records for an entry with no named-ledger record.

    Only a row that names the entry as its *primary* subject counts: a backticked name in the
    parenthetical right after the row's bold headline (`**Prose claim proved**
    (`Lemma2_1_iterationCount`)`), or else the first backticked identifier after the headline.  The headline decides: refuted-without-proof or partial
    gives None (nothing proved as a whole); "corrected" gives corrected; "restricted" or "only for"
    gives restricted; any other
    headline with "proved" gives printed ("partial" headlines, see `partial_lead`, give None).  An entry whose name is marked corrected or restricted
    also counts when any proving row names it.  Otherwise None."""
    for row in coverage_rows:
        scope = row["scope"]
        rest = re.sub(r"^\s*\*\*.+?\*\*", "", scope, count=1)
        paren = re.match(r"\s*\(([^)]*)\)", rest)
        if paren:  # "**Proved** (`Remark4_1`, `Remark4_2`): ..." names every entry in the parenthetical
            subjects = re.findall(r"`([^`]+)`", paren.group(1))
        else:
            first = re.search(r"`([^`]+)`", rest)
            subjects = [first.group(1)] if first else []
        if name not in [x.rsplit(".", 1)[-1] for x in subjects]:
            continue
        lead = row["lead"].lower()
        if not lead:
            continue
        if partial_lead(lead) or ("refuted" in lead and "proved" not in lead) or "proved" not in lead:
            return None
        if "corrected" in lead:
            return "corrected"
        if re.search(r"restricted|\bonly for\b", lead):
            return "restricted"
        return "printed"
    # A variant entry (name marked corrected / restricted) that a proving row names anywhere, e.g.
    # "**Printed statement refuted; corrected and restricted variants proved.** ... `X_corrected` proves".
    marker = re.search(r"(corrected)|(positiven|restricted|causal|_k\d)", name.lower())
    if marker:
        for row in coverage_rows:
            lead = row["lead"].lower()
            if "proved" in lead and not lead.startswith("partial") and \
                    re.search(r"`(?:[\w.']*\.)?%s`" % re.escape(name), row["scope"]):
                return "corrected" if marker.group(1) else "restricted"
    return None


def classify(name: str, ledger_kind: str | None, scope: str = "", coverage_rows: list | None = None) -> str:
    """Variant of one statement entry; mirrors site/reader/lean.py `classify`.

    A name marker (`_corrected`, `_positiveN`, `_restricted`, `_causal`, `_K2`) always wins.
    Entries with a named-ledger record follow the ledger.  Entries without one (prose
    claims, displays, remarks) take the variant from the coverage-ledger row that names them
    (`coverage_variant`); with no such row they are `printed` only when the name has no
    suffix after the source number (`Remark4_1`, `Eq_mdp_value_Q`), else `restricted`."""
    low = name.lower()
    if "corrected" in low:
        return "corrected"
    if re.search(r"positiven|restricted|causal|_k\d", low) or scope.strip().lower().startswith("restricted"):
        return "restricted"
    if ledger_kind == "certified_named_results":
        return "printed"
    if ledger_kind == "proved_variants":
        return "restricted"
    cov = coverage_variant(name, coverage_rows or [])
    if cov:
        return cov
    if re.fullmatch(r"(Thm|Lemma|Claim|Remark)\d+_\d+", name) or name.startswith("Eq_"):
        return "printed"
    return "restricted"


def tex_key(path: str) -> str:
    """Normalize `source/upstream/tex/chapters/x.tex`, `chapters/x.tex`, `x.tex` to `x.tex`."""
    return path.rsplit("/", 1)[-1]


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


class Reader:
    """Working-tree file access; the site passes a git-revision reader with the same API."""

    def __init__(self, root: Path):
        self.root = root

    def show(self, path: str) -> str:
        return (self.root / path).read_text(encoding="utf-8")

    def ls(self, prefix: str) -> list:
        base = self.root / prefix
        return sorted(str(p.relative_to(self.root)).replace(os.sep, "/") for p in base.rglob("*") if p.is_file())


# ---------------------------------------------------------------------------------------
# derivation


def statement_files(reader) -> list:
    files = [f for f in reader.ls("Formalization/Statements") if re.search(r"/Ch\d+\.lean$", f)]
    return sorted(files, key=lambda f: int(re.search(r"Ch(\d+)\.lean$", f).group(1)))


def parse_statement_entries(reader) -> list:
    out = []
    for f in statement_files(reader):
        text = reader.show(f)
        proofs_path = f.replace(".lean", "Proofs.lean")
        try:
            ptext = reader.show(proofs_path)
        except (OSError, RuntimeError):
            ptext = ""
        holds = {}
        for m in HOLDS_RE.finditer(ptext):
            start = m.start()
            nxt = HOLDS_RE.search(ptext, m.end())
            body = ptext[start:nxt.start() if nxt else len(ptext)]
            holds[m.group(1)] = {"line": ptext.count("\n", 0, start) + 1, "body": body}
        for m in DECL_RE.finditer(text):
            doc = m.group("doc")
            line = text.count("\n", 0, m.start()) + 1
            name = m.group("name")
            ns = namespace_at(text, line)
            full = f"{ns}.{name}" if ns else name
            pns = ""
            wrapper = None
            if name in holds:
                pns = namespace_at(ptext, holds[name]["line"])
                wrapper = f"{pns}.{name}_holds" if pns else f"{name}_holds"
            out.append({
                "name": name, "full": full, "file": f, "line": line, "doc": doc,
                "labels": [l for l in LABEL_RE.findall(doc) if ".tex" not in l],
                "ranges": [{"file": tex_key(r[0]), "line_start": int(r[1]), "line_end": int(r[2] or r[1])}
                           for r in RANGE_RE.findall(doc)],
                "issues": CID_RE.findall(doc),
                "wrapper": wrapper, "wrapper_file": proofs_path if wrapper else None,
                "wrapper_body": holds.get(name, {}).get("body", ""),
            })
    return out


def parse_issue_ids(text: str) -> set:
    ids = set()
    for line in text.splitlines():
        m = re.match(r"#+\s+.*\bC(\d+)\b", line)
        if m:
            ids.add(m.group(1))
    return ids


def parse_coverage(text: str) -> list:
    rows = []
    for n, line in enumerate(text.splitlines(), 1):
        if not line.startswith("| ") or line.startswith("| ---") or line.startswith("| Source item"):
            continue
        cells = split_md_row(line)
        if len(cells) < 3:
            continue
        lead = re.match(r"\s*\*\*(.+?)\*\*", cells[2])
        rows.append({"line": n, "item": cells[0], "evidence": cells[1], "scope": cells[2], "raw": line,
                     "lead": lead.group(1) if lead else ""})
    return rows


def overlap(a0, a1, b0, b1) -> int:
    return max(0, min(a1, b1) - max(a0, b0) + 1)


class Builder:
    def __init__(self, reader):
        self.reader = reader
        self.inputs = {}
        inv_text = self.read("docs/source-inventory.json")
        self.inv = json.loads(inv_text)
        self.ledger = json.loads(self.read("docs/named-result-status.json"))
        self.coverage = parse_coverage(self.read("docs/COVERAGE.md"))
        self.issue_ids = parse_issue_ids(self.read("docs/SOURCE-ISSUES.md"))
        self.entries = parse_statement_entries(reader)
        for f in statement_files(reader):
            self.read(f)
            try:
                self.read(f.replace(".lean", "Proofs.lean"))
            except (OSError, RuntimeError):
                pass
        self.warnings: list = []

        self.inv_entries = self.inv["entries"]
        self.by_id = {e["id"]: e for e in self.inv_entries}
        self.label_owner = {}
        for e in self.inv_entries:
            for lab in e.get("labels", []):
                self.label_owner.setdefault(lab, e)
        for lab in self.inv.get("labels", []):
            if lab["label"] not in self.label_owner and lab.get("owner_id") in self.by_id:
                self.label_owner[lab["label"]] = self.by_id[lab["owner_id"]]
        self.label_line = {l["label"]: (tex_key(l["source"]["file"]), l["source"]["line_start"])
                           for l in self.inv.get("labels", [])}
        self.by_number = {}
        for e in self.inv_entries:
            if e["kind"] in NAMED_KINDS + PROSE_KINDS and e.get("number"):
                self.by_number[(e["kind"], e["number"])] = e

    def read(self, path: str) -> str:
        text = self.reader.show(path)
        self.inputs[path] = sha256(text)
        return text

    # helpers ------------------------------------------------------------------------
    @staticmethod
    def ranges(e) -> list:
        return [(tex_key(r["file"]), r["line_start"], r["line_end"]) for r in e.get("source_ranges", [])]

    def containing_result(self, file: str, line: int):
        """Smallest named/remark entry whose statement range contains the line."""
        best = None
        for e in self.inv_entries:
            if e["kind"] not in NAMED_KINDS + PROSE_KINDS:
                continue
            for f, a, b in self.ranges(e):
                if f == file and a <= line <= b and (best is None or b - a < best[1]):
                    best = (e, b - a)
        return best[0] if best else None

    def entry_for_range(self, rng: dict):
        """Inventory entry a statement-index range points at: a numbered result or remark
        with the largest overlap, else the smallest display containing it."""
        f, a, b = rng["file"], rng["line_start"], rng["line_end"]
        best, best_ov = None, 0
        for e in self.inv_entries:
            if e["kind"] not in NAMED_KINDS + PROSE_KINDS:
                continue
            for ef, ea, eb in self.ranges(e):
                ov = overlap(a, b, ea, eb) if ef == f else 0
                if ov > best_ov:
                    best, best_ov = e, ov
        if best:
            return best
        cands = []
        for e in self.inv_entries:
            if e["kind"] not in ("display", "subequations"):
                continue
            for ef, ea, eb in self.ranges(e):
                if ef == f and overlap(a, b, ea, eb):
                    cands.append((eb - ea, e))
        return min(cands, key=lambda x: x[0])[1] if cands else None

    def ledger_entry(self, rec):
        sid, lab = rec.get("source_inventory_id"), rec.get("source_label")
        if sid and sid in self.by_id:
            return self.by_id[sid]
        if lab and lab in self.label_owner:
            return self.label_owner[lab]
        return None

    # main ---------------------------------------------------------------------------
    def build(self) -> dict:
        nodes: dict = {}

        def node_for(e):
            if e["id"] not in nodes:
                named = e["kind"] in NAMED_KINDS
                nodes[e["id"]] = {
                    "id": e["id"], "labels": list(e.get("labels", [])),
                    "number": e.get("number") or next((r["number"] for r in e.get("rows", []) if r.get("number")),
                                                      None),
                    "kind": e["kind"], "class": "named" if named else "prose",
                    "chapter": e.get("chapter"), "title_tex": e.get("title_tex"),
                    "tex": [{"file": r["file"].split("/tex/", 1)[-1], "line_start": r["line_start"],
                             "line_end": r["line_end"]} for r in e.get("source_ranges", [])],
                    "statement_entries": [], "proof_wrappers": [], "library_exports": [],
                    "ledger_records": [], "coverage_rows": [], "issues": set(), "evidence": [],
                    "refutations_cited": [], "partial_lead": False, "refuted_lead": False, "uses": [],
                }
            return nodes[e["id"]]

        for e in self.inv_entries:
            if e["kind"] in NAMED_KINDS + PROSE_KINDS:
                node_for(e)

        # ledger records ------------------------------------------------------------
        recorded = {}
        self.entry_node = {}
        for kind in ("certified_named_results", "proved_variants"):
            for rec in self.ledger.get(kind, []):
                e = self.ledger_entry(rec)
                if e is None:
                    raise SystemExit(f"ledger record {rec.get('lean_statement')} has no inventory entry")
                n = node_for(e)
                recorded[rec["lean_statement"]] = (kind, rec, n)
                n["ledger_records"].append({"ledger": "certified" if kind == "certified_named_results" else "variant",
                                            "name": rec.get("name"), "lean_statement": rec["lean_statement"]})
                if rec.get("evidence"):
                    n["evidence"].append(rec["evidence"])
                n["issues"].update(CID_RE.findall(rec.get("statement_scope", "")))
                # Refutations of the printed form named in the record (data only: a recorded node is proved).
                for name in re.findall(r"(?<![\w.'])(?:[\w']+\.)*(not_[\w']*printed[\w']*)",
                                       " ".join(str(rec.get(k, "")) for k in ("lean_export", "statement_scope"))):
                    if name not in n["refutations_cited"]:
                        n["refutations_cited"].append(name)
                exp = rec.get("component_exports") or rec.get("lean_export", "")
                if isinstance(exp, list):
                    exp = " ".join(map(str, exp))
                for name in QUALIFIED_RE.findall(exp):
                    name = name.rstrip(".,;")
                    if name not in n["library_exports"] and not name.endswith("_holds"):
                        n["library_exports"].append(name)

        # statement-index entries -----------------------------------------------------
        for ent in self.entries:
            rec = recorded.get(ent["full"])
            if rec:
                kind, record, n = rec
                variant = classify(ent["name"], kind, record.get("statement_scope", ""))
            else:
                kind, record = None, None
                target = None
                first = ent["ranges"][0] if ent["ranges"] else None
                # A cited label whose own source range overlaps the docstring's first range
                # wins (it names the display or remark itself); otherwise go by range.
                # An equation label may sit a few lines before a prose claim cited by a single
                # line ("x.tex:2585-"), so displays get a 3-line tolerance; results get none.
                for lab in ent["labels"]:
                    o = self.label_owner.get(lab)
                    slack = 3 if o and o["kind"] in ("display", "subequations") else 0
                    if o and first and o["kind"] not in CONTEXT_KINDS and any(
                            f == first["file"] and overlap(a - slack, b + slack,
                                                           first["line_start"], first["line_end"])
                            for f, a, b in self.ranges(o)):
                        target = o
                        break
                for r in ent["ranges"]:
                    if target:
                        break
                    target = self.entry_for_range(r)
                if target is None:
                    for lab in ent["labels"]:
                        if lab in self.label_owner:
                            target = self.label_owner[lab]
                            break
                if target is None:
                    self.warnings.append(f"statement entry {ent['full']} matches no inventory entry")
                    continue
                n = node_for(target)
                variant = classify(ent["name"], None, "", self.coverage)
            self.entry_node[ent["full"]] = n["id"]
            attached = [n]
            if not rec:
                # A joint entry (one Prop for several displays) also belongs to every other cited
                # label whose own range lies inside the docstring's first range, unless it is
                # nested inside the main target (a row of the same subequations block).
                first = ent["ranges"][0] if ent["ranges"] else None
                main_ranges = self.ranges(self.by_id[n["id"]]) if n["id"] in self.by_id else []
                for lab in ent["labels"]:
                    o = self.label_owner.get(lab)
                    if not o or not first or o["kind"] in CONTEXT_KINDS or o["id"] == n["id"]:
                        continue
                    inside = any(f == first["file"] and first["line_start"] <= a and b <= first["line_end"]
                                 for f, a, b in self.ranges(o))
                    nested = any(f == mf and ma <= a and b <= mb
                                 for f, a, b in self.ranges(o) for mf, ma, mb in main_ranges)
                    if inside and not nested and node_for(o) not in attached:
                        attached.append(node_for(o))
            for n in attached:
                n["statement_entries"].append({
                    "name": ent["full"], "variant": variant,
                    "ledger": None if kind is None else ("certified" if kind == "certified_named_results" else "variant"),
                    "file": ent["file"], "line": ent["line"]})
                n["issues"].update(ent["issues"])
                if ent["wrapper"]:
                    n["proof_wrappers"].append(ent["wrapper"])
                if not rec:
                    # exports applied by the wrapper (unrecorded entries have no ledger export field)
                    for name in QUALIFIED_RE.findall(ent["wrapper_body"]):
                        if ".Statements." in "." + name or name.endswith("_holds") or name in n["library_exports"]:
                            continue
                        if name.startswith("StatisticalRL."):
                            n["library_exports"].append(name)

        # COVERAGE rows ------------------------------------------------------------------
        for row in self.coverage:
            labels = [l for l in re.findall(r"`([^`]+)`", row["item"]) if l in self.label_owner]
            targets = []
            for lab in labels:
                e = self.label_owner[lab]
                if e["kind"] in NAMED_KINDS + PROSE_KINDS or e["id"] in nodes:
                    targets.append(e)
                elif e["kind"] in CONTEXT_KINDS:
                    continue
                else:
                    f, line = self.label_line.get(lab, (None, None))
                    c = self.containing_result(f, line) if f else None
                    targets.append(c or e)
            if not labels:
                labels = [l for l in re.findall(r"[A-Za-z][\w-]*:[^\s,;()`]+", row["item"])
                          if l.rstrip(".") in self.label_owner]
                for lab in labels:
                    e = self.label_owner[lab.rstrip(".")]
                    if e["kind"] not in CONTEXT_KINDS:
                        targets.append(e)
            if not targets:
                numbered = []
                for m in NUMBERED_REF_RE.finditer(row["item"]):
                    kind = m.group(1).lower()
                    nums = [m.group(2)] + re.findall(r"\d+\.\d+", m.group(3) or "")
                    numbered += [self.by_number[(kind, x)] for x in nums if (kind, x) in self.by_number]
                # "lines a–b" plus a link to Statements/ChN.lean: the entries of that file whose
                # cited range lies inside a–b (in the same .tex file as a numbered result named
                # by the row, if any).  This finds prose claims such as "minimax optimality of
                # Theorem 3.9 ... (claim at 2585)", which then take precedence.
                ranged = []
                after = row["item"].split("lines ", 1)[1] if "lines " in row["item"] else ""
                spans = [(int(x), int(y)) for x, y in re.findall(r"(\d+)[–-](\d+)", after)]
                files = set(re.findall(r"Statements/(Ch\d+)\.lean", row["evidence"]))
                tex_files = {f for e in numbered for f, _, _ in self.ranges(e)}
                for a, b in (spans if files else []):
                    for ent in self.entries:
                        r = ent["ranges"][0] if ent["ranges"] else None
                        if r and ent["file"].endswith(tuple(f"/{f}.lean" for f in files)) \
                                and a <= r["line_start"] and r["line_end"] <= b and ent["full"] in self.entry_node \
                                and (not tex_files or r["file"] in tex_files):
                            ranged.append(self.by_id[self.entry_node[ent["full"]]])
                targets = ranged or numbered
            if not targets:
                self.warnings.append(f"COVERAGE.md:{row['line']} matches no inventory result: {row['item']}")
                continue
            lead = row["lead"].lower()
            for e in dict((t["id"], t) for t in targets).values():
                n = node_for(e)
                n["coverage_rows"].append(row["line"])
                n["issues"].update(coverage_issue_ids(row["raw"]))
                for name in REFUTATION_RE.findall(row["raw"]):
                    if name not in n["refutations_cited"]:
                        n["refutations_cited"].append(name)
                # Fail-closed headline: a row whose bold lead says Partial, or says refuted without
                # saying anything is proved, overrides a proved status (with a warning).
                if partial_lead(lead):
                    n["partial_lead"] = True
                if re.search(r"\brefuted\b", lead) and "proved" not in lead:
                    n["refuted_lead"] = True

        # statuses ------------------------------------------------------------------------
        for n in nodes.values():
            variants = [s["variant"] for s in n["statement_entries"]
                        if n["class"] == "prose" or s["ledger"] is not None]
            if n["class"] == "named":
                proved = bool(n["ledger_records"])
            else:
                proved = bool(n["statement_entries"]) and bool(n["coverage_rows"])
            if proved and (n["partial_lead"] or n["refuted_lead"]):
                self.warnings.append(f"{n['id']}: proved by the ledgers, but a COVERAGE headline says "
                                     f"{'partial' if n['partial_lead'] else 'refuted'}; the headline wins")
                proved = False
            if proved:
                st = ("printed" if "printed" in variants else "corrected" if "corrected" in variants
                      else "restricted")
            elif n["refutations_cited"]:
                st = "refuted"
            elif n["partial_lead"] or n["statement_entries"]:
                st = "partial"
            else:
                st = "open" if n["class"] == "named" else "prose-claim"
            n["statement_status"] = st
            n["proof_status"] = "proved" if proved else ("refuted" if st == "refuted" else "open")
            n["issues"] = sorted((c for c in n["issues"] if c in self.issue_ids), key=int)
            n["issues"] = [f"C{c}" for c in n["issues"]]
            n["evidence"] = sorted(set(n["evidence"]))
            n["proof_wrappers"] = sorted(set(n["proof_wrappers"]))

        # prune prose nodes created only by unmatched context (none expected) and order --------
        self.add_uses(nodes)
        self.printed_with_cited_printed(nodes)
        order = {e["id"]: i for i, e in enumerate(self.inv_entries)}
        node_list = sorted(nodes.values(), key=lambda n: order.get(n["id"], 10 ** 9))
        context = [{"id": e["id"], "labels": e.get("labels", []), "kind": e["kind"], "number": e.get("number"),
                    "chapter": e.get("chapter"),
                    "tex": [{"file": r["file"].split("/tex/", 1)[-1], "line_start": r["line_start"],
                             "line_end": r["line_end"]} for r in e.get("source_ranges", [])]}
                   for e in self.inv_entries if e["kind"] in CONTEXT_KINDS]
        summary = self.summary(node_list)
        return {
            "schema_version": SCHEMA_VERSION,
            "generated_by": "scripts/gen_nodes.py",
            "notice": ("Generated file; do not edit. Status is derived from the reviewed ledgers. "
                       "The formalization of the monograph is INCOMPLETE. `uses` edges are unreviewed "
                       "candidates from TeX cross-references."),
            "source": {"arxiv_id": self.inv["source"]["arxiv_id"], "main_sha256": self.inv["source"]["main_sha256"]},
            "inputs_sha256": dict(sorted(self.inputs.items())),
            "vocabulary": {"statement_status": list(STATEMENT_STATUSES), "proof_status": list(PROOF_STATUSES)},
            "summary": summary,
            "nodes": node_list,
            "context": context,
            "warnings": sorted(set(self.warnings)),
        }

    def add_uses(self, nodes: dict):
        # spans: (file, a, b) owned by a node -- its statement and its proof(s)
        spans = []
        for nid, n in nodes.items():
            e = self.by_id.get(nid)
            if not e:
                continue
            for f, a, b in self.ranges(e):
                spans.append((f, a, b, nid))
        for e in self.inv_entries:
            if e["kind"] not in ("proof", "proof_region"):
                continue
            owners = []
            adj = e.get("adjacent_result_candidate")
            if adj in nodes:
                owners.append(adj)
            for lab in PROOF_TITLE_RE.findall(e.get("title_tex") or ""):
                o = self.label_owner.get(lab)
                if o and o["id"] in nodes and o["kind"] in NAMED_KINDS + PROSE_KINDS:
                    owners.append(o["id"])
            for nid in dict.fromkeys(owners):
                for f, a, b in self.ranges(e):
                    spans.append((f, a, b, nid))
        context_ids = {e["id"] for e in self.inv_entries if e["kind"] in CONTEXT_KINDS}
        edges: dict = {}
        for ref in self.inv.get("references", []):
            if ref.get("kind") != "cross_reference":
                continue
            f, line = tex_key(ref["source"]["file"]), ref["source"]["line_start"]
            inside = [(b - a, nid) for sf, a, b, nid in spans if sf == f and a <= line <= b]
            if not inside:
                continue
            owner = min(inside)[1]
            for lab in ref.get("targets", []):
                t = self.label_owner.get(lab)
                if t is None:
                    continue
                if t["id"] in nodes or t["id"] in context_ids:
                    tid = t["id"]
                else:
                    lf, ll = self.label_line.get(lab, (None, None))
                    c = self.containing_result(lf, ll) if lf else None
                    if c is None or c["id"] not in nodes:
                        continue
                    tid = c["id"]
                if tid == owner:
                    continue
                key = (owner, tid)
                if key not in edges:
                    edges[key] = {"id": tid, "label": lab, "via": "tex-ref", "reviewed": False,
                                  "target": "context" if tid in context_ids else "node",
                                  "file": f, "line": line}
        for (owner, _), edge in sorted(edges.items(), key=lambda kv: (kv[0][0], kv[1]["line"], kv[1]["id"])):
            nodes[owner]["uses"].append(edge)

    @staticmethod
    def printed_with_cited_printed(nodes: dict):
        fp = {nid: n["statement_status"] == "printed" and n["proof_status"] == "proved" for nid, n in nodes.items()}
        changed = True
        while changed:
            changed = False
            for nid, n in nodes.items():
                if fp[nid] and any(u["target"] == "node" and not fp.get(u["id"], False) for u in n["uses"]):
                    fp[nid] = False
                    changed = True
        for nid, n in nodes.items():
            n["printed_with_cited_printed"] = fp[nid]

    def summary(self, node_list: list) -> dict:
        named = [n for n in node_list if n["class"] == "named"]
        by_chapter: dict = {}
        for n in node_list:
            ch = by_chapter.setdefault(n["chapter"], {"named": {s: 0 for s in STATEMENT_STATUSES},
                                                      "prose": {s: 0 for s in STATEMENT_STATUSES},
                                                      "named_total": 0, "named_proved": 0,
                                                      "named_printed_with_cited_printed": 0})
            ch[n["class"]][n["statement_status"]] += 1
            if n["class"] == "named":
                ch["named_total"] += 1
                ch["named_proved"] += n["proof_status"] == "proved"
                ch["named_printed_with_cited_printed"] += n["printed_with_cited_printed"]
        # Cross-check: count distinct ledger keys (inventory id, else source label) that name a
        # numbered inventory entry, directly from the ledger and inventory fields.  This shares
        # the ledger's own keys with the node pass, so it guards the node bookkeeping, not the
        # ledger's correctness.
        named_ids = {e["id"] for e in self.inv_entries if e["kind"] in NAMED_KINDS}
        named_label_id = {l: e["id"] for e in self.inv_entries if e["kind"] in NAMED_KINDS
                          for l in e.get("labels", [])}
        ledger_ids = set()
        for kind in ("certified_named_results", "proved_variants"):
            for rec in self.ledger.get(kind, []):
                sid, lab = rec.get("source_inventory_id"), rec.get("source_label")
                if sid in named_ids:
                    ledger_ids.add(sid)
                elif lab in named_label_id:
                    ledger_ids.add(named_label_id[lab])
        proved_named = sum(n["proof_status"] == "proved" for n in named)
        if proved_named != len(ledger_ids):
            raise SystemExit(f"node count {proved_named} disagrees with ledger count {len(ledger_ids)}")
        kinds = self.inv["counts"]["by_kind"]
        inventory_named = sum(kinds.get(k, 0) for k in NAMED_KINDS)
        if len(named) != inventory_named:
            raise SystemExit(f"{len(named)} named nodes but the inventory has {inventory_named}")
        tally = lambda pred: sum(1 for n in node_list if pred(n))  # noqa: E731
        return {
            "named_results_in_inventory": inventory_named,
            "named_results_with_ledger_record": len(ledger_ids),
            "named_by_statement_status": {s: tally(lambda n, s=s: n["class"] == "named" and n["statement_status"] == s)
                                          for s in STATEMENT_STATUSES},
            "named_printed_with_cited_printed": tally(lambda n: n["class"] == "named" and n["printed_with_cited_printed"]),
            "prose_nodes": tally(lambda n: n["class"] == "prose"),
            "prose_by_statement_status": {s: tally(lambda n, s=s: n["class"] == "prose" and n["statement_status"] == s)
                                          for s in STATEMENT_STATUSES},
            "uses_edges": sum(len(n["uses"]) for n in node_list),
            "uses_edges_reviewed": 0,
            "context_items": {k: kinds.get(k, 0) for k in CONTEXT_KINDS},
            "source_gap_candidates": kinds.get("source_gap_candidate", 0),
            "by_chapter": dict(sorted(by_chapter.items(), key=lambda kv: int(kv[0] or 0))),
        }


def build(reader) -> dict:
    data = Builder(reader).build()
    for n in data["nodes"]:
        n["issues"] = list(n["issues"])
    return data


# ---------------------------------------------------------------------------------------
# NEXT.md


def node_title(n: dict) -> str:
    kind = n["kind"].capitalize() if n["kind"] not in ("display", "subequations") else "Display"
    num = f" {n['number']}" if n.get("number") and kind != "Display" else ""
    lab = f" `{n['labels'][0]}`" if n["labels"] else ""
    return f"{kind}{num}{lab}"


def tex_cite(n: dict) -> str:
    return ", ".join(f"`{t['file']}:{t['line_start']}–{t['line_end']}`" for t in n["tex"][:1])


def render_next(data: dict) -> str:
    nodes = {n["id"]: n for n in data["nodes"]}
    s = data["summary"]
    lines = [
        "# What to formalize next",
        "",
        "<!-- Generated by `python3 scripts/gen_nodes.py` from docs/graph/nodes.json; do not edit by hand. -->",
        "",
        f"Generated from `docs/graph/nodes.json` (inventory sha256 "
        f"`{data['inputs_sha256'].get('docs/source-inventory.json', '')[:12]}`, ledger sha256 "
        f"`{data['inputs_sha256'].get('docs/named-result-status.json', '')[:12]}`). "
        "Regenerate with `python3 scripts/gen_nodes.py`; check freshness with `--check`.",
        "",
        "**The formalization of the monograph is INCOMPLETE.** "
        f"{s['named_results_with_ledger_record']} of the {s['named_results_in_inventory']} numbered theorems, "
        "lemmas and claims have a reviewed ledger record (printed, corrected or restricted form); prose claims, "
        "algorithms, definitions and source-gap candidates are outside that count.",
        "",
        "Dependencies (`uses`) are candidates read from TeX cross-references inside each result and its proof. "
        "They are **not reviewed**: a reference can be a remark or a comparison rather than a logical dependency, "
        "and a real dependency can be cited without `\\ref`.",
        "",
    ]

    def open_uses(n):
        return [u for u in n["uses"] if u["target"] == "node" and nodes[u["id"]]["proof_status"] != "proved"]

    def row(n, extra=""):
        issues = (" · " + ", ".join(n["issues"])) if n["issues"] else ""
        note = (" · COVERAGE note only, no statement entry" if n["coverage_rows"]
                and n["statement_status"] == "prose-claim" else "")
        return f"- {node_title(n)} — {tex_cite(n)} · statement `{n['statement_status']}`{issues}{note}{extra}"

    named_open = [n for n in data["nodes"] if n["class"] == "named" and n["proof_status"] != "proved"]
    lines += ["## Open numbered results", "",
              "Numbered theorems, lemmas and claims with no reviewed ledger record "
              "(including those whose printed form is refuted in Lean).", ""]
    lines += [row(n) for n in named_open] or ["- none"]
    lines.append("")

    ready = [n for n in data["nodes"] if n["proof_status"] != "proved" and not open_uses(n)]
    blocked = [n for n in data["nodes"] if n["proof_status"] != "proved" and open_uses(n)]
    lines += ["## Ready: open nodes whose candidate uses are all proved", "",
              "Open numbered results and prose claims (remarks, displayed claims) whose every unreviewed "
              "TeX-reference dependency on another node is proved. Definitions, assumptions and algorithms "
              "are context, not blockers.", ""]
    for cls, title in (("named", "Numbered results"), ("prose", "Remarks and displayed claims")):
        part = [n for n in ready if n["class"] == cls]
        lines += [f"### {title} ({len(part)})", ""]
        lines += [row(n) for n in part] or ["- none"]
        lines.append("")
    lines += [f"### Blocked: some candidate use is not proved ({len(blocked)})", ""]
    for n in blocked:
        deps = ", ".join(node_title(nodes[u["id"]]) for u in open_uses(n))
        lines.append(row(n, f" · waits on {deps}"))
    if not blocked:
        lines.append("- none")
    lines.append("")

    strengthen = [n for n in data["nodes"] if n["statement_status"] in ("corrected", "restricted")]
    lines += ["## Proved only in corrected or restricted form", "",
              "The printed statement is not proved as printed. Each needs either a proof of the printed "
              "form or a source-issue record explaining why it fails.", ""]
    lines += [row(n) for n in strengthen] or ["- none"]
    lines.append("")

    partial = [n for n in data["nodes"] if n["statement_status"] == "partial"]
    lines += ["## Partial", "", "A COVERAGE row marked partial, or a statement entry without its reviewed record.", ""]
    lines += [row(n) for n in partial] or ["- none"]
    lines.append("")

    ctx = s["context_items"]
    lines += ["## Other obligations outside the numbered-result count", "",
              f"- Prose nodes (remarks and displayed claims): {s['prose_nodes']}, of which "
              + ", ".join(f"{v} {k}" for k, v in s["prose_by_statement_status"].items() if v) + ".",
              f"- Algorithms: {ctx['algorithm']}; definitions: {ctx['definition']}; assumptions: "
              f"{ctx['assumption']} (context items, not nodes; edges to them are recorded but never block).",
              f"- Source-gap candidates in the inventory: {s['source_gap_candidates']} (see `docs/SOURCE-ISSUES.md`).",
              "- Unlabelled prose claims not listed in `docs/COVERAGE.md` are not tracked as nodes.",
              ""]
    if data["warnings"]:
        lines += ["## Generator warnings", ""] + [f"- {w}" for w in data["warnings"]] + [""]
    return "\n".join(lines)


def dumps(data: dict) -> str:
    return json.dumps(data, ensure_ascii=False, indent=1) + "\n"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="fail if the committed outputs are stale; write nothing")
    ap.add_argument("--summary", action="store_true", help="print the summary only; write nothing")
    ap.add_argument("--root", default=str(ROOT), help=argparse.SUPPRESS)
    args = ap.parse_args(argv)
    root = Path(args.root)
    data = build(Reader(root))
    outputs = {NODES_PATH: dumps(data), NEXT_PATH: render_next(data) + "\n"}
    if args.summary:
        print(json.dumps(data["summary"], indent=1))
        return 0
    if args.check:
        stale = []
        for path, text in outputs.items():
            p = root / path
            if not p.is_file() or p.read_text(encoding="utf-8") != text:
                stale.append(path)
        if stale:
            print("stale generated files (run python3 scripts/gen_nodes.py): " + ", ".join(stale))
            return 1
        print(f"ok: {NODES_PATH} and {NEXT_PATH} are current")
        return 0
    for path, text in outputs.items():
        p = root / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
    s = data["summary"]
    print(f"wrote {NODES_PATH} ({len(data['nodes'])} nodes, {s['uses_edges']} unreviewed uses edges) and {NEXT_PATH}")
    print(f"named results with ledger record: {s['named_results_with_ledger_record']} of {s['named_results_in_inventory']}")
    for w in data["warnings"]:
        print("warning: " + w)
    return 0


if __name__ == "__main__":
    sys.exit(main())

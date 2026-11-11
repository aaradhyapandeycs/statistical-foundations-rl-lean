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
* Printed-statement failures come from the explicit ledger field `printed_refuted` in
  named-result-status.json, keyed by source label (or `id:<inventory id>`): `lean` lists the Lean
  theorems refuting the printed statement under `reading` (null if none), `paper` says a paper argument
  (not Lean-checked) shows a failure.  The node's `refutations_cited` are the short names of `lean`.
  The old name heuristic (backticked `not_..._printed...` in a COVERAGE row, or such a name in a ledger
  record) is kept only as a cross-check: every name it finds must be listed in the field, or the
  generator fails.  G4 in static_gates.py checks that the listed names resolve.
* `refuted`: nothing is proved for the node and the field lists a Lean refutation.  A node that
  is proved in some form is never `refuted`; it carries the refuted marker instead.  A node with
  only a paper argument gets the separate `fails-paper` marker ("appears to fail").  A field record with
  `"kind"` other than `counterexample` (the default) gets its own marker instead of `refuted` and is
  excluded from every refuted count, tallied separately: `boundary` (only a degenerate boundary or
  parameter point, repaired by a domain restriction), `reading` (marker `reading-dependent`: fails only
  under a stated reading of an ambiguous printed form), `domain` (fails only outside a standing or assumed
  parameter range), `ill-posed` (the printed formula is undefined at the point; Lean's value is a
  convention).  These kinds may also qualify a paper-only failure.
  `partial`: a COVERAGE row whose bold lead starts with "Partial" or proves only part of the
  item ("First two sentences proved"), or a statement entry without the reviewed record it needs.
* Source-issue ids are read from ledger scopes and docstrings as `Cnn` (not `C1 = 2`), and from
  COVERAGE rows only as links (`SOURCE-ISSUES.md#Cnn`, `[Cnn]`), since rows use constants C1, C2.
* Fail-closed: if a numbered result with a ledger record has a COVERAGE headline that says "Partial",
  or says "refuted" without saying anything is proved, the headline wins and a warning is emitted.
  For a remark or display the COVERAGE row is its only reviewed record, so such a headline simply
  makes the node partial (no warning), and its statement entries are not counted.
* `open`: a named node with nothing recorded.  `prose-claim`: a prose node with no
  statement entry (it may have a COVERAGE note).
* A joint statement entry (one Prop for several displays) is attached to every cited
  label whose range lies inside the entry's first cited range.
* Closing statuses for a prose node that is not proved, from the bold headline of a COVERAGE row:
  `**Implied by `X`**` -> `implied` (each X a statement entry with one `_holds` wrapper whose own node
  is proved; `implied_variant` carries X's suffix: corrected > restricted > printed),
  `**Explanatory (no mathematical claim)**` -> `explanatory`, `**Out of scope: cited result**` ->
  `cited-out-of-scope` (the row must contain a dated `user decision YYYY-MM-DD` anchor; the generator
  fails otherwise).  None of them is ever counted as proved (proof status stays `open`); they are
  counted in `summary.closing_not_proved`.  For readiness, `implied` and `explanatory` nodes do not
  block dependants; `cited-out-of-scope` nodes do.  A closing row whose item matches no node (an
  unlabelled prose claim) is kept in `closing_rows_without_node`; for closing rows only a numbered
  reference at the start of the item ("Remark 2.1, ...") names the item.
* An unrecorded entry whose docstring's first range contains a whole remark belongs
  to that remark (Remark 6.3 citing `eq:concentrate-infinite` inside its own range).  A joint entry also
  attaches to a label the docstring pairs with its own range ("`eq:x`, `chapters/f.tex:a–b`") when a
  proving COVERAGE row lists that label in its item (before any parenthesis) and names the entry.
* A closing row may never target a numbered result (the generator fails).
* An unrecorded entry whose range target is an unlabelled display lying inside the "lines a–b" span of a
  reviewed COVERAGE row that lists a label the entry cites (as its item) and names the entry belongs to
  that label's item (`reviewed_parent`; the rectangles and ellipsoids inside `eq:convex.Cdelta`).
* Gate G7 (write and `--check` modes): the generator fails if any node is incomplete only because its
  entries have no reviewed status record, or if any statement entry matches no inventory item.
* A `_holds` wrapper's body ends at the next top-level command (declaration, `open`, `section`, `end`,
  docstring, comment), so later names never count as exports it applies.
* A COVERAGE row headed **Supporting ...** records infrastructure for other rows: it is never
  attached to a node and never counts as proving anything (listed in `supporting_rows`).
* `printed_with_cited_printed`: statement `printed`, proof `proved`, and every node reachable
  through `uses` is also proved as printed.  `uses` edges are candidates read from the TeX
  cross-references (`\\ref`, `\\eqref`, ...) inside the result and its proof; they are
  classified by `docs/graph/uses-review.json` (an AI critic and an independent AI verifier; not
  author-reviewed): an edge with a review entry has `"reviewed": true` and a `verdict`, an edge without
  one stays `"reviewed": false`.  Only `proof-dependency` (and unreviewed) edges count as dependencies
  (`is_dependency`); `definition` and `comparison` edges are context and `wrong-target` edges are kept
  in the node but used nowhere.  Edges the review added have `"via": "review"`.  The review file naming
  an edge that does not exist is a stale record and fails like gate G7.  This flag is not a certificate
  that the cited results are what the proof actually needs: it deliberately stays conservative and
  counts every cited node except a `wrong-target` edge.

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
CLASSES_PATH = "docs/issue-classes.json"
ISSUE_CLASSES = ("A", "B", "C", "D")
REVIEW_PATH = "docs/graph/uses-review.json"
# Verdicts of the reviewed `uses` record.  Only `proof-dependency` is a dependency; an unreviewed edge
# (no review entry) and an `unclear` one stay dependencies so that a gap in the record never unblocks work.
REVIEW_VERDICTS = ("proof-dependency", "definition", "comparison", "wrong-target", "unclear")
DEPENDENCY_VERDICTS = (None, "proof-dependency", "unclear")


def is_dependency(u: dict) -> bool:
    """A `uses` edge that counts as a dependency: a node target whose verdict is not definition,
    comparison or wrong-target (those are shown as context only)."""
    return u["target"] == "node" and u.get("verdict") in DEPENDENCY_VERDICTS
SCHEMA_VERSION = 1

NAMED_KINDS = ("theorem", "lemma", "claim")
PROSE_KINDS = ("remark",)            # always nodes, even with nothing recorded
CONTEXT_KINDS = ("definition", "assumption", "algorithm")  # edge targets only, never "proved"
# `implied`, `explanatory` and `cited-out-of-scope` close a prose node's NEXT entry without proving it:
# they are counted separately and never as proved (proof status stays `open`).
CLOSING_STATUSES = ("implied", "explanatory", "cited-out-of-scope")
STATEMENT_STATUSES = ("printed", "corrected", "restricted", "refuted", "partial") + CLOSING_STATUSES + \
    ("related", "open", "prose-claim")
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


# Closing headlines (bold lead of a COVERAGE row).  See `closing_kind`.
IMPLIED_LEAD_RE = re.compile(r"^implied by\b", re.I)
EXPLANATORY_LEAD_RE = re.compile(r"^explanatory\b", re.I)
OUT_OF_SCOPE_LEAD_RE = re.compile(r"^out of scope: cited result\b", re.I)
# A row recording infrastructure that supports other rows ("**Supporting infrastructure ...**") names no
# source item: it is never attached to a node, never counts as proving anything, and is not warned about.
SUPPORTING_LEAD_RE = re.compile(r"^supporting\b", re.I)
# A cited-out-of-scope row must carry a dated user-decision anchor (never inferred).
DECISION_ANCHOR_RE = re.compile(r"\buser decision (\d{4}-\d{2}-\d{2})\b", re.I)


def closing_kind(lead: str) -> str | None:
    """`implied`, `explanatory` or `cited-out-of-scope` for a closing COVERAGE headline, else None.

    `**Implied by `X`**` (X: statement entries, each with exactly one `_holds` wrapper; the status
    carries X's suffix), `**Explanatory (no mathematical claim)**`, `**Out of scope: cited result**`
    (only with a dated `user decision YYYY-MM-DD` anchor in the row)."""
    lead = lead.strip()
    if IMPLIED_LEAD_RE.match(lead):
        return "implied"
    if EXPLANATORY_LEAD_RE.match(lead):
        return "explanatory"
    if OUT_OF_SCOPE_LEAD_RE.match(lead):
        return "cited-out-of-scope"
    return None


# ---------------------------------------------------------------------------------------
# Reader-facing vocabulary: exactly four labels, derived only from a node's fields.

SITE_LABELS = {
    "stated": ("proved as stated", "st-stated"),
    "corrected": ("proved with corrections", "st-corrected"),
    "restricted": ("proved under restrictions", "st-restricted"),
    "incomplete": ("incomplete", "st-incomplete"),
}
SITE_LABEL_ORDER = ("stated", "corrected", "restricted", "incomplete")
# Orthogonal markers shown after the label (word + icon, never colour only).
MARKERS = {
    "refuted": "✕ printed statement refuted in Lean",
    "fails-paper": "⚠ printed statement appears to fail (paper argument)",
    "boundary": "∂ printed statement fails at a boundary case (domain repaired)",
    "reading-dependent": "◇ printed statement fails only under a stated reading",
    "domain": "⊘ printed statement fails only outside its assumed domain",
    "ill-posed": "∅ printed formula is undefined at the point (Lean value is a convention)",
    "new-proof": "new proof",
    "also-corrected": "also corrected",
}
# Optional ledger-record fields (named-result-status.json) and their defaults.
REFUTATION_KINDS = ("counterexample", "boundary", "reading", "domain", "ill-posed")
# ledger `kind` -> site marker.  Only `counterexample` is a plain refutation (marker `refuted`, or `fails-paper`
# when only a paper argument shows it); every other kind is a qualified failure with its own marker.
KIND_MARKER = {"boundary": "boundary", "reading": "reading-dependent", "domain": "domain", "ill-posed": "ill-posed"}
# per-kind marker counts in the summary (`named_<key>_marker`, `prose_<key>_marker`, `<key>_marker_nodes`)
KIND_COUNT_KEYS = {"boundary": "boundary", "reading-dependent": "reading", "domain": "domain",
                   "ill-posed": "illposed"}
PROOF_ORIGINS = ("source-proof", "source-proof-repaired", "own-proof:source-cites", "own-proof:source-omits",
                 "unclassified")
CORRECTION_STATUSES = ("proposed-by-project", "author-confirmed")
STATUS_OVERRIDES = ("incomplete",)  # downgrade-only
INCOMPLETE_REASONS = {
    "refuted": "nothing proved",
    "partial": "partial",
    "open": "not yet formalized",
    "prose-claim": "not yet formalized",
    "implied": "implied by a proved entry (not separately proved)",
    "cited-out-of-scope": "cited from the literature; out of scope (project decision)",
    "related": "a related statement is proved, not the printed result",
}


# Sub-reason of a remark or display whose only entries have no reviewed COVERAGE row (gate G7 fails on it).
UNRECORDED_SUB_REASON = "Lean statement without a reviewed status record"


def record_fields(rec: dict) -> dict:
    """The optional reader fields of one ledger record, validated, with safe defaults."""
    origin = rec.get("proof_origin") or "unclassified"
    if origin not in PROOF_ORIGINS:
        raise SystemExit(f"{rec.get('lean_statement')}: unknown proof_origin {origin!r}")
    corr = rec.get("correction_status") or "proposed-by-project"
    if corr not in CORRECTION_STATUSES:
        raise SystemExit(f"{rec.get('lean_statement')}: unknown correction_status {corr!r}")
    override = rec.get("status_override")
    if override is not None and override not in STATUS_OVERRIDES:
        raise SystemExit(f"{rec.get('lean_statement')}: status_override may only be 'incomplete' "
                         f"(downgrade only), got {override!r}")
    note = rec.get("display_note") or ""
    if not isinstance(note, str):
        raise SystemExit(f"{rec.get('lean_statement')}: display_note must be a string")
    return {"proof_origin": origin, "correction_status": corr, "status_override": override,
            "display_note": note.strip()}


def display_name(n: dict) -> str:
    """Reader name of a node ("Theorem 7.11", "Eq. (5.146)"); never an internal id."""
    kind = n.get("kind", "")
    num = n.get("number")
    if kind in ("display", "subequations"):
        if num:
            return f"Eq. ({num})"
        t = (n.get("tex") or [{}])[0]
        if t:
            a, b = t.get("line_start"), t.get("line_end")
            where = f'{t["file"].rsplit("/", 1)[-1]}:{a}' + (f"–{b}" if b and b != a else "")
            return f"Unnumbered display ({where})"
        return "Unnumbered display"
    word = kind.capitalize() if kind else "Item"
    return f"{word} {num}".strip() if num else word


def site_label(n: dict):
    """(label key or None, markers, sub_reason) for a node: the only status the reader shows.

    proved + printed -> stated; proved + corrected -> corrected; proved + restricted -> restricted
    (with an "also corrected" marker when a counted entry is corrected too); everything else ->
    incomplete with a sub-reason; `explanatory` (no mathematical claim) -> no label at all.
    Markers: `refuted` for a Lean refutation of the printed form (ledger field `printed_refuted`);
    `fails-paper` when only a paper argument shows a failure; `new-proof` when every ledger record's
    proof_origin is an own proof."""
    st, pf = n["statement_status"], n["proof_status"]
    markers = []
    pr = n.get("printed_refuted") or {}
    if pr.get("kind") in KIND_MARKER and (n.get("refutations_cited") or pr.get("paper")):
        markers.append(KIND_MARKER[pr["kind"]])
    elif n.get("refutations_cited") or st == "refuted":
        markers.append("refuted")
    elif pr.get("paper"):
        markers.append("fails-paper")
    origins = n.get("proof_origins") or []
    if pf == "proved" and origins and all(o.startswith("own-proof") for o in origins):
        markers.append("new-proof")
    if st == "explanatory":
        return None, markers, "no mathematical claim"
    if pf == "proved" and st in ("printed", "corrected", "restricted"):
        key = {"printed": "stated", "corrected": "corrected", "restricted": "restricted"}[st]
        if key == "restricted" and any("corrected" in e["name"].rsplit(".", 1)[-1].lower()
                                       for e in n.get("statement_entries", []) if e.get("counted", True)):
            markers.append("also-corrected")
        return key, markers, ""
    if st == "implied" and n.get("implied_variant"):
        sub = f'implied by a proved {n["implied_variant"]} entry (not separately proved)'
    elif st == "partial" and n.get("statement_entries") and not n.get("coverage_rows"):
        sub = UNRECORDED_SUB_REASON
    else:
        sub = INCOMPLETE_REASONS.get(st, "not yet formalized")
    return "incomplete", markers, sub


def parse_printed_refuted(field: dict, issue_ids) -> dict:
    """Validate the ledger field `printed_refuted` (keys starting with `_` are comments)."""
    if not isinstance(field, dict):
        raise SystemExit("printed_refuted must map source labels to records")
    out = {}
    for key, rec in field.items():
        if key.startswith("_"):
            continue
        if not isinstance(rec, dict) or set(rec) - {"lean", "paper", "reading", "issues", "kind"}:
            raise SystemExit(f"printed_refuted[{key!r}]: fields are lean, paper, reading, issues, kind")
        kind = rec.get("kind", "counterexample")
        if kind not in REFUTATION_KINDS:
            raise SystemExit(f"printed_refuted[{key!r}].kind must be one of {', '.join(REFUTATION_KINDS)}")
        lean = rec.get("lean")
        if lean is not None and (not isinstance(lean, list) or not lean
                                 or not all(isinstance(x, str) and x.startswith("StatisticalRL.") for x in lean)):
            raise SystemExit(f"printed_refuted[{key!r}].lean must be null or a nonempty list of StatisticalRL names")
        paper = rec.get("paper")
        if not isinstance(paper, bool):
            raise SystemExit(f"printed_refuted[{key!r}].paper must be true or false")
        if lean is None and not paper:
            raise SystemExit(f"printed_refuted[{key!r}]: neither a Lean refutation nor a paper argument")
        reading = rec.get("reading")
        if not isinstance(reading, str) or not reading.strip():
            raise SystemExit(f"printed_refuted[{key!r}].reading must state the reading under which it fails")
        issues = rec.get("issues") or []
        bad = [c for c in issues if not re.fullmatch(r"C\d+", str(c)) or c[1:] not in issue_ids]
        if bad:
            raise SystemExit(f"printed_refuted[{key!r}]: unknown source issue(s) {bad}")
        out[key] = {"lean": list(lean) if lean else None, "paper": paper, "reading": reading.strip(),
                    "issues": list(issues), "kind": kind}
    return out


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


def classify(name: str, ledger_kind: str | None, scope: str = "", coverage_rows: list | None = None,
             declared: str | None = None) -> str:
    """Variant of one statement entry; mirrors site/reader/lean.py `classify`.

    An explicit ledger field `statement_variant: "restricted"` wins over everything (used where an
    entry named `_corrected` is also restricted, e.g. `Thm7_11_corrected_halfspace`); it may only
    downgrade (to restricted), never declare a variant `printed` or `corrected`.
    A name marker (`_corrected`, `_positiveN`, `_restricted`, `_causal`, `_K2`) always wins.
    Entries with a named-ledger record follow the ledger.  Entries without one (prose
    claims, displays, remarks) take the variant from the coverage-ledger row that names them
    (`coverage_variant`); with no such row they are `printed` only when the name has no
    suffix after the source number (`Remark4_1`, `Eq_lemma_VarP_V_bound`), else `restricted`."""
    if declared is not None:
        if declared != "restricted":
            raise SystemExit(f"{name}: statement_variant may only be 'restricted', got {declared!r}")
        return "restricted"
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


def worst_variant(variants: list) -> str:
    """corrected > restricted > printed: an implication from a variant inherits its suffix."""
    for v in ("corrected", "restricted"):
        if v in variants:
            return v
    return "printed"


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


# A wrapper's body ends at the next top-level command (a line starting in column 0 with a command
# keyword, a doc or block comment, a line comment or an attribute), not at the next `_holds`, so names in
# a following docstring, `open ... in` line or section header never count as exports the wrapper applies.
TOPLEVEL_RE = re.compile(r"^(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*"
                         r"(?:theorem|lemma|def|abbrev|instance|example|structure|inductive|class|axiom|opaque|"
                         r"section|end|namespace|open|variable|universe|set_option|attribute|export|mutual|"
                         r"import|omit|include)\b|^/-|^--|^@\[|^#", re.M)


def wrapper_end(text: str, pos: int) -> int:
    """Offset where the top-level command that contains `pos` ends (the next command line, else EOF)."""
    nl = text.find("\n", pos)
    m = TOPLEVEL_RE.search(text, nl + 1) if nl >= 0 else None
    return m.start() if m else len(text)


def label_paired_ranges(doc: str) -> dict:
    """For each backticked label in a docstring, the `.tex:a–b` range written right after it (before the
    next label), e.g. "`eq:bellman_consistency-V`, `chapters/prelim.tex:210–223`"."""
    labs = [(m.start(), m.end(), m.group(1)) for m in LABEL_RE.finditer(doc) if ".tex" not in m.group(1)]
    out: dict = {}
    for i, (_, end, lab) in enumerate(labs):
        stop = labs[i + 1][0] if i + 1 < len(labs) else len(doc)
        r = RANGE_RE.search(doc, end, stop)
        if r and lab not in out:
            out[lab] = {"file": tex_key(r.group(1)), "line_start": int(r.group(2)),
                        "line_end": int(r.group(3) or r.group(2))}
    return out


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
            body = ptext[start:wrapper_end(ptext, m.end())]
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
                "label_ranges": label_paired_ranges(doc),
                "issues": CID_RE.findall(doc),
                "wrapper": wrapper, "wrapper_file": proofs_path if wrapper else None,
                "wrapper_body": holds.get(name, {}).get("body", ""),
            })
    return out


def parse_issue_classes(rec: dict) -> dict:
    """Validate docs/issue-classes.json: class definitions, class-tagged items and the per-entry classes."""
    if not isinstance(rec, dict) or set(ISSUE_CLASSES) != set(rec.get("definitions") or {}):
        raise SystemExit(f"{CLASSES_PATH}: `definitions` must give exactly the classes {', '.join(ISSUE_CLASSES)}")
    items = rec.get("items")
    if not isinstance(items, list) or not items:
        raise SystemExit(f"{CLASSES_PATH}: `items` must be a nonempty list")
    names = set()
    for it in items:
        if not isinstance(it, dict) or set(it) != {"item", "class", "labels", "record"}:
            raise SystemExit(f"{CLASSES_PATH}: each item has exactly item, class, labels, record: {it!r}")
        if it["class"] not in ISSUE_CLASSES:
            raise SystemExit(f"{CLASSES_PATH}: item {it['item']!r} has class {it['class']!r}; "
                             f"allowed: {', '.join(ISSUE_CLASSES)}")
        if it["item"] in names:
            raise SystemExit(f"{CLASSES_PATH}: duplicate item {it['item']!r}")
        names.add(it["item"])
        if not (isinstance(it["labels"], list) and it["labels"] and all(isinstance(x, str) for x in it["labels"])):
            raise SystemExit(f"{CLASSES_PATH}: item {it['item']!r} needs a nonempty list of source labels")
        if it["record"] is not None and not isinstance(it["record"], str):
            raise SystemExit(f"{CLASSES_PATH}: item {it['item']!r}: record must be a string or null")
    entries = rec.get("errata_entries")
    if not isinstance(entries, dict) or not all(k.isdigit() and v in ISSUE_CLASSES for k, v in entries.items()):
        raise SystemExit(f"{CLASSES_PATH}: `errata_entries` must map entry numbers to classes")
    return {"definitions": dict(rec["definitions"]), "items": items, "errata_entries": dict(entries)}


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
        # Reader notes for statement entries without a ledger record (keyed by entry name; optional).
        notes = self.ledger.get("entry_display_notes") or {}
        if not isinstance(notes, dict) or not all(isinstance(v, str) for v in notes.values()):
            raise SystemExit("entry_display_notes must map entry names to strings")
        self.entry_notes = {k: v.strip() for k, v in notes.items() if not k.startswith("_") and v.strip()}
        self.issue_ids = parse_issue_ids(self.read("docs/SOURCE-ISSUES.md"))
        self.printed_refuted = parse_printed_refuted(self.ledger.get("printed_refuted") or {}, self.issue_ids)
        self.issue_classes = parse_issue_classes(json.loads(self.read(CLASSES_PATH)))
        self.entries = parse_statement_entries(reader)
        for f in statement_files(reader):
            self.read(f)
            try:
                self.read(f.replace(".lean", "Proofs.lean"))
            except (OSError, RuntimeError):
                pass
        self.warnings: list = []
        self.review = self.load_review(reader)

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

    def load_review(self, reader) -> list:
        try:
            text = self.read(REVIEW_PATH)
        except (OSError, RuntimeError):
            return []
        rec = json.loads(text)
        out = []
        for i, r in enumerate(rec.get("edges", [])):
            if r.get("verdict") not in REVIEW_VERDICTS or r.get("source") not in ("candidate", "added-by-review"):
                raise SystemExit(f"{REVIEW_PATH}: edge {i} has an unknown verdict or source")
            out.append(r)
        return out

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

    def row_confirms_joint(self, label: str, name: str) -> bool:
        for row in self.coverage:
            # only the item proper: a label in parentheses after it is context ("(`eq:TV` ...)")
            if f"`{label}`" in row["item"].split("(", 1)[0] and "proved" in row["lead"].lower() and \
                    not partial_lead(row["lead"]) and \
                    re.search(r"`(?:[\w.']*\.)?%s`" % re.escape(name), row["evidence"] + " " + row["scope"]):
                return True
        return False

    def reviewed_parent(self, ent: dict, target: dict):
        """The labelled item an unrecorded entry belongs to when its range target is an unlabelled display.

        An unlabelled display (no label, so no COVERAGE row can name it) lying inside the line span of a
        reviewed COVERAGE row is part of that row's item: the rectangles and ellipsoids at
        `inference.tex:198–213` belong to the rule `eq:convex.Cdelta` (row item "lines 187–213"). The entry
        moves to the item's node when the entry cites the item's label, the row lists that label as its item
        (before any parenthesis), names the entry, and its first "lines a–b" span contains the display."""
        if target["kind"] not in ("display", "subequations") or target.get("labels"):
            return None
        tr = self.ranges(target)
        for lab in ent["labels"]:
            o = self.label_owner.get(lab)
            if not o or o["kind"] in CONTEXT_KINDS or o["id"] == target["id"]:
                continue
            files = {f for f, _, _ in self.ranges(o)}
            for row in self.coverage:
                if SUPPORTING_LEAD_RE.match(row["lead"].strip()) or closing_kind(row["lead"]):
                    continue
                head = row["item"].split("(", 1)[0]
                if f"`{lab}`" not in head or "lines " not in head:
                    continue
                if not re.search(r"`(?:[\w.']*\.)?%s`" % re.escape(ent["name"]), row["evidence"] + " " + row["scope"]):
                    continue
                m = re.search(r"(\d+)[–-](\d+)", head.split("lines ", 1)[1])
                if m and all(f in files and int(m.group(1)) <= a and b <= int(m.group(2)) for f, a, b in tr):
                    return o
        return None

    def closing_info(self, row: dict, closing: str, entry_variant: dict) -> dict:
        """Validate a closing COVERAGE row (fail-closed) and return what the node records."""
        info = {"line": row["line"], "kind": closing, "entries": [], "variant": None, "anchor": None}
        if closing == "implied":
            names = re.findall(r"`([^`]+)`", row["lead"])
            if not names:
                raise SystemExit(f"COVERAGE.md:{row['line']}: 'Implied by' names no statement entry")
            for nm in names:
                hits = [e for e in self.entries if nm in (e["name"], e["full"])]
                if len(hits) != 1 or not hits[0]["wrapper"]:
                    raise SystemExit(f"COVERAGE.md:{row['line']}: 'Implied by `{nm}`' must name exactly one "
                                     f"statement entry with a `_holds` wrapper")
                info["entries"].append(hits[0]["full"])
            info["variant"] = worst_variant([entry_variant.get(f, classify(f.rsplit(".", 1)[-1], None, "",
                                                                         self.coverage))
                                             for f in info["entries"]])
        elif closing == "cited-out-of-scope":
            m = DECISION_ANCHOR_RE.search(row["raw"])
            if not m:
                raise SystemExit(f"COVERAGE.md:{row['line']}: 'Out of scope: cited result' needs a dated "
                                 f"'user decision YYYY-MM-DD' anchor")
            info["anchor"] = m.group(1)
        return info

    def apply_printed_refuted(self, nodes: dict):
        """Attach the ledger field `printed_refuted` to its nodes and cross-check the name heuristic."""
        claimed = {}
        for key, info in self.printed_refuted.items():
            if key.startswith("id:"):
                n = nodes.get(key[3:])
            else:
                e = self.label_owner.get(key)
                n = nodes.get(e["id"]) if e else None
            if n is None:
                raise SystemExit(f"printed_refuted[{key!r}]: no tracked numbered result, remark or display")
            if n["id"] in claimed:
                raise SystemExit(f"printed_refuted: {key!r} and {claimed[n['id']]!r} name the same item")
            claimed[n["id"]] = key
            n["printed_refuted"] = dict(info, key=key)
        for n in nodes.values():
            info = n["printed_refuted"]
            lean = [x.rsplit(".", 1)[-1] for x in ((info or {}).get("lean") or [])]
            stray = [x for x in n["refutations_cited"] if x not in lean]
            if stray:
                raise SystemExit(f"{n['id']}: the ledgers cite Lean refutation(s) {', '.join(stray)} by name, but "
                                 f"named-result-status.json `printed_refuted` does not list them for this item; "
                                 f"add them (or correct the citation)")
            n["refutations_cited"] = lean

    def apply_issue_classes(self, nodes: dict):
        """Tag nodes with the issue classes of the items (docs/issue-classes.json) whose labels they carry.
        Labels may be `id:<inventory id>` for unlabelled results. Fails on a label that is not in the inventory, and on an item none of whose labels names a node."""
        def owner(lab):  # a source label, or `id:<inventory id>` as in printed_refuted
            return self.by_id.get(lab[3:]) if lab.startswith("id:") else self.label_owner.get(lab)

        for it in self.issue_classes["items"]:
            bad = [lab for lab in it["labels"] if owner(lab) is None]
            if bad:
                raise SystemExit(f"{CLASSES_PATH}: item {it['item']!r} names label(s) not in the inventory "
                                 f"(stale?): {', '.join(bad)}")
            hit = {owner(lab)["id"] for lab in it["labels"] if owner(lab)["id"] in nodes}
            if not hit:
                raise SystemExit(f"{CLASSES_PATH}: no label of item {it['item']!r} names a tracked node")
            for nid in hit:
                nodes[nid]["issue_class_items"].append({"item": it["item"], "class": it["class"]})
        for n in nodes.values():
            n["issue_classes"] = sorted({x["class"] for x in n["issue_class_items"]})

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
                    "closing": {}, "reviewed_rows": 0,
                    "display_name": "", "proof_origins": [], "display_notes": [], "correction_status": None,
                    "status_override": None, "printed_refuted": None, "issue_class_items": [], "issue_classes": [],
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
                f = record_fields(rec)
                n["ledger_records"].append({"ledger": "certified" if kind == "certified_named_results" else "variant",
                                            "name": rec.get("name"), "lean_statement": rec["lean_statement"],
                                            "proof_origin": f["proof_origin"],
                                            "correction_status": f["correction_status"],
                                            "status_override": f["status_override"]})
                if f["display_note"]:
                    n["display_notes"].append({"entry": rec["lean_statement"], "note": f["display_note"]})
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
                variant = classify(ent["name"], kind, record.get("statement_scope", ""),
                                   declared=record.get("statement_variant"))
            else:
                kind, record = None, None
                target = None
                first = ent["ranges"][0] if ent["ranges"] else None
                # A remark or numbered result whose whole range lies inside the docstring's first
                # range is the entry's subject (Remark 6.3 cites `eq:concentrate-infinite` inside its own
                # range; the entry belongs to the remark, not to the display).
                # (remarks only: a long first range such as a proof span may contain a numbered result
                # that the entry merely cites)
                inner = [(b - a, e) for e in self.inv_entries if e["kind"] in PROSE_KINDS
                         for f, a, b in self.ranges(e) if first and f == first["file"]
                         and first["line_start"] <= a and b <= first["line_end"]]
                if inner:
                    target = max(inner, key=lambda x: x[0])[1]
                # A cited label whose own source range overlaps the docstring's first range
                # wins (it names the display or remark itself); otherwise go by range.
                # An equation label may sit a few lines before a prose claim cited by a single
                # line ("x.tex:2585-"), so displays get a 3-line tolerance; results get none.
                for lab in ent["labels"]:
                    if target:
                        break
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
                target = self.reviewed_parent(ent, target) or target
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
                    # inside the first range, or inside the range the docstring pairs with this label
                    # ("`eq:x`, `chapters/f.tex:a–b`", a second display of a joint entry) when a proving
                    # COVERAGE row lists the label as its item and names the entry (the reviewed ledger
                    # confirms the joint reading; a label cited as context is not attached)
                    paired = ent["label_ranges"].get(lab) if self.row_confirms_joint(lab, ent["name"]) else None
                    inside = any(any(r and f == r["file"] and r["line_start"] <= a and b <= r["line_end"]
                                     for r in (first, paired))
                                 for f, a, b in self.ranges(o))
                    nested = any(f == mf and ma <= a and b <= mb
                                 for f, a, b in self.ranges(o) for mf, ma, mb in main_ranges)
                    if inside and not nested and node_for(o) not in attached:
                        attached.append(node_for(o))
            extra = self.entry_notes.get(ent["name"]) or self.entry_notes.get(ent["full"])
            for n in attached:
                if extra and not any(d["entry"] == ent["full"] for d in n["display_notes"]):
                    n["display_notes"].append({"entry": ent["full"], "note": extra})
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
        entry_variant = {}
        for n in nodes.values():
            for se in n["statement_entries"]:
                entry_variant.setdefault(se["name"], se["variant"])
        self.closing_rows = []   # closing rows matching no node (unlabelled prose claims)
        self.supporting_rows = []
        for row in self.coverage:
            if SUPPORTING_LEAD_RE.match(row["lead"].strip()):
                self.supporting_rows.append(row["line"])
                continue
            closing = closing_kind(row["lead"])
            info = self.closing_info(row, closing, entry_variant) if closing else None
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
                    # A closing row names its own item first ("Remark 2.1, ..."); a later mention
                    # ("read-off after Theorem 3.2") is context, not the item.
                    if closing and m.start() > 0:
                        continue
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
            if not targets and closing:
                self.closing_rows.append(dict(info, item=row["item"]))
                continue
            if not targets:
                self.warnings.append(f"COVERAGE.md:{row['line']} matches no inventory result: {row['item']}")
                continue
            lead = row["lead"].lower()
            for e in dict((t["id"], t) for t in targets).values():
                if closing and e["kind"] in NAMED_KINDS:
                    raise SystemExit(f"COVERAGE.md:{row['line']}: a numbered result ({e['id']}) can never be "
                                     f"closed as {closing}; only remarks and displays can")
                n = node_for(e)
                n["coverage_rows"].append(row["line"])
                if closing:
                    n["closing"].setdefault(closing, []).append(info)
                else:
                    n["reviewed_rows"] += 1
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

        # printed-statement failures: the ledger field decides; the name heuristic must agree --------
        self.apply_printed_refuted(nodes)
        self.apply_issue_classes(nodes)

        # statuses ------------------------------------------------------------------------
        for n in nodes.values():
            over_names = {r["lean_statement"] for r in n["ledger_records"] if r["status_override"]}
            variants = [s["variant"] for s in n["statement_entries"]
                        if (n["class"] == "prose" or s["ledger"] is not None) and s["name"] not in over_names]
            # A ledger record with `status_override: "incomplete"` never counts as proving the node
            # (downgrade only); the node is proved only by its other records.
            counted = [r for r in n["ledger_records"] if not r["status_override"]]
            overridden = len(counted) < len(n["ledger_records"])
            if n["class"] == "named":
                proved = bool(counted)
            else:
                # a closing row (implied / explanatory / out of scope) never makes an entry count as proved
                proved = bool(n["statement_entries"]) and n["reviewed_rows"] > 0
            if proved and (n["partial_lead"] or n["refuted_lead"]):
                # A numbered result's ledger record and its COVERAGE headline disagree: warn. For a remark
                # or display the COVERAGE row is its only reviewed record, so the headline is its status.
                if n["class"] == "named":
                    self.warnings.append(f"{n['id']}: proved by the ledgers, but a COVERAGE headline says "
                                         f"{'partial' if n['partial_lead'] else 'refuted'}; the headline wins")
                proved = False
            if proved:
                st = ("printed" if "printed" in variants else "corrected" if "corrected" in variants
                      else "restricted")
            elif overridden and n["class"] == "named":
                st = "related"
            elif n["partial_lead"]:
                # part of the item is proved (a refutation of the rest is shown by the marker)
                st = "partial"
            elif n["refutations_cited"]:
                st = "refuted"
            elif n["closing"] and not n["reviewed_rows"]:
                # The reviewed row classifies the item (a joint entry may cite a step-definition display).
                # A remainder cited out of scope keeps the node out of scope; otherwise implied beats
                # explanatory (a node with an implied part and explanatory sentences).
                st = next(k for k in ("cited-out-of-scope", "implied", "explanatory") if k in n["closing"])
            elif n["statement_entries"]:
                st = "partial"
            else:
                st = "open" if n["class"] == "named" else "prose-claim"
            n["statement_status"] = st
            n["proof_status"] = "proved" if proved else ("refuted" if st == "refuted" else "open")
            imp = [i for i in n["closing"].get("implied", [])]
            n["implied_by"] = sorted({x for i in imp for x in i["entries"]})
            n["implied_variant"] = (worst_variant([i["variant"] for i in imp]) if st == "implied" else None)
            n["decision_anchors"] = sorted({i["anchor"] for i in n["closing"].get("cited-out-of-scope", [])})
            n["closing_rows"] = {k: sorted(i["line"] for i in v) for k, v in sorted(n["closing"].items())}
            del n["closing"], n["reviewed_rows"]
            n["issues"] = sorted((c for c in n["issues"] if c in self.issue_ids), key=int)
            n["issues"] = [f"C{c}" for c in n["issues"]]
            n["evidence"] = sorted(set(n["evidence"]))
            n["proof_wrappers"] = sorted(set(n["proof_wrappers"]))
            over = {r["lean_statement"] for r in n["ledger_records"] if r["status_override"]}
            for se in n["statement_entries"]:
                se["counted"] = se["name"] not in over and (proved if n["class"] == "prose" else se["ledger"] is not None)
            n["status_override"] = "incomplete" if overridden and not counted else None
            n["proof_origins"] = sorted({r["proof_origin"] for r in counted} - {"unclassified"}) if proved else []
            corr = [r["correction_status"] for r in counted]
            n["correction_status"] = (("author-confirmed" if corr and all(c == "author-confirmed" for c in corr)
                                       else "proposed-by-project")
                                      if proved and st in ("corrected", "restricted") or n["refutations_cited"]
                                      else None)
            n["display_name"] = display_name(n)
            lab, markers, sub = site_label(n)
            n["site_label"], n["site_markers"], n["site_sub_reason"] = lab, markers, sub

        # an implication is only as good as the entry it comes from: that entry's node must be proved
        for n in nodes.values():
            for full in n["implied_by"]:
                src = nodes.get(self.entry_node.get(full, ""))
                if src is None or src["proof_status"] != "proved":
                    raise SystemExit(f"{n['id']}: implied by `{full}`, whose own node is not proved")

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
                       "The formalization of the monograph is INCOMPLETE. `uses` edges are TeX cross-references "
                       "classified by an AI critic and verifier (docs/graph/uses-review.json), not author-reviewed."),
            "source": {"arxiv_id": self.inv["source"]["arxiv_id"], "main_sha256": self.inv["source"]["main_sha256"]},
            "inputs_sha256": dict(sorted(self.inputs.items())),
            "vocabulary": {"statement_status": list(STATEMENT_STATUSES), "proof_status": list(PROOF_STATUSES)},
            "summary": summary,
            "issue_class_ledger": self.issue_classes,
            "nodes": node_list,
            "context": context,
            "closing_rows_without_node": self.closing_rows,
            "supporting_rows": self.supporting_rows,
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
        # reviewed verdicts: each review entry must name an existing edge (candidate) or an existing
        # owner and target not already linked (added-by-review); anything else is a stale record
        problems = []
        for r in self.review:
            owner, tid, f, line = r["owner"], r["target"], tex_key(r["file"]), r["line"]
            where = f"{REVIEW_PATH}: {r['source']} edge {owner} -> {tid} ({f}:{line})"
            if r["source"] == "candidate":
                edge = edges.get((owner, tid))
                if edge is None or edge["file"] != f or edge["line"] != line:
                    problems.append(where + " matches no candidate uses edge (stale review entry)")
                    continue
            else:
                if owner not in nodes or tid not in nodes or tid == owner:
                    problems.append(where + " names a node that does not exist (stale review entry)")
                    continue
                if (owner, tid) in edges:
                    problems.append(where + " duplicates an existing edge")
                    continue
                edge = edges[(owner, tid)] = {"id": tid, "label": (nodes[tid]["labels"] or [tid])[0], "via": "review",
                                              "reviewed": False, "target": "node", "file": f, "line": line}
            if edge.get("reviewed"):
                problems.append(where + " duplicates another review entry")
                continue
            edge["reviewed"] = True
            edge["verdict"] = r["verdict"]
        self.warnings += problems
        for (owner, _), edge in sorted(edges.items(), key=lambda kv: (kv[0][0], kv[1]["line"], kv[1]["id"])):
            nodes[owner]["uses"].append(edge)

    @staticmethod
    def printed_with_cited_printed(nodes: dict):
        fp = {nid: n["statement_status"] == "printed" and n["proof_status"] == "proved" for nid, n in nodes.items()}
        changed = True
        while changed:
            changed = False
            for nid, n in nodes.items():
                if fp[nid] and any(u["target"] == "node" and u.get("verdict") != "wrong-target"
                                and not fp.get(u["id"], False) for u in n["uses"]):
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
                                                      "named_printed_with_cited_printed": 0,
                                                      "named_by_label": {k: 0 for k in SITE_LABEL_ORDER},
                                                      "prose_by_label": dict({k: 0 for k in SITE_LABEL_ORDER},
                                                                             no_claim=0),
                                                      "named_refuted_marker": 0, "prose_refuted_marker": 0,
                                                      "named_fails_paper_marker": 0, "prose_fails_paper_marker": 0,
                                                      **{f"{c}_{k}_marker": 0 for k in KIND_COUNT_KEYS.values()
                                                         for c in ("named", "prose")}})
            ch[n["class"]][n["statement_status"]] += 1
            lab = n["site_label"] or "no_claim"
            ch[f'{n["class"]}_by_label'][lab] += 1
            ch[f'{n["class"]}_refuted_marker'] += "refuted" in n["site_markers"]
            ch[f'{n["class"]}_fails_paper_marker'] += "fails-paper" in n["site_markers"]
            for mk, k in KIND_COUNT_KEYS.items():
                ch[f'{n["class"]}_{k}_marker'] += mk in n["site_markers"]
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
        overridden_ids = set()
        for kind in ("certified_named_results", "proved_variants"):
            for rec in self.ledger.get(kind, []):
                sid, lab = rec.get("source_inventory_id"), rec.get("source_label")
                if rec.get("status_override"):
                    key = sid if sid in named_ids else named_label_id.get(lab)
                    if key:
                        overridden_ids.add(key)
                    continue
                if sid in named_ids:
                    ledger_ids.add(sid)
                elif lab in named_label_id:
                    ledger_ids.add(named_label_id[lab])
        # A named label without a counted record must be "named_by_label" incomplete, never proved.
        for n in named:
            if n["site_label"] is None:
                raise SystemExit(f"{n['id']}: a numbered result can never be unlabelled")
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
            # never part of any proved count: nodes plus unlabelled COVERAGE rows with a closing headline
            "closing_not_proved": {k: {"nodes": tally(lambda n, k=k: n["statement_status"] == k),
                                       "rows_without_node": sum(1 for r in self.closing_rows if r["kind"] == k)}
                                   for k in CLOSING_STATUSES},
            # Reader labels (exactly four; `no_claim` = explanatory prose, excluded from every denominator).
            "named_by_label": {k: tally(lambda n, k=k: n["class"] == "named" and n["site_label"] == k)
                               for k in SITE_LABEL_ORDER},
            "named_refuted_marker": tally(lambda n: n["class"] == "named" and "refuted" in n["site_markers"]),
            "named_overridden_incomplete": len(overridden_ids - ledger_ids),
            "prose_by_label": dict({k: tally(lambda n, k=k: n["class"] == "prose" and n["site_label"] == k)
                                    for k in SITE_LABEL_ORDER},
                                   no_claim=tally(lambda n: n["class"] == "prose" and n["site_label"] is None)),
            "prose_refuted_marker": tally(lambda n: n["class"] == "prose" and "refuted" in n["site_markers"]),
            "refuted_marker_nodes": tally(lambda n: "refuted" in n["site_markers"]),
            # printed statements that appear to fail by a paper argument only (no Lean refutation)
            "named_fails_paper_marker": tally(lambda n: n["class"] == "named" and "fails-paper" in n["site_markers"]),
            "prose_fails_paper_marker": tally(lambda n: n["class"] == "prose" and "fails-paper" in n["site_markers"]),
            "fails_paper_marker_nodes": tally(lambda n: "fails-paper" in n["site_markers"]),
            # qualified failures, one count per ledger kind (boundary, reading, domain, ill-posed); none is a refuted count
            **{f"{c}_{k}_marker": tally(lambda n, c=c, mk=mk: n["class"] == c and mk in n["site_markers"])
               for mk, k in KIND_COUNT_KEYS.items() for c in ("named", "prose")},
            **{f"{k}_marker_nodes": tally(lambda n, mk=mk: mk in n["site_markers"])
               for mk, k in KIND_COUNT_KEYS.items()},
            # issue classes A-D (docs/issue-classes.json): per item, per numbered erratum entry, per node
            "issue_classes": {
                "by_item": {c: sum(i["class"] == c for i in self.issue_classes["items"]) for c in ISSUE_CLASSES},
                "by_entry": {c: sum(v == c for v in self.issue_classes["errata_entries"].values())
                             for c in ISSUE_CLASSES},
                "by_node": {c: tally(lambda n, c=c: c in n["issue_classes"]) for c in ISSUE_CLASSES}},
            "refutation_theorems": len({x for n in node_list if "refuted" in n["site_markers"]
                                        for x in n["refutations_cited"]}),
            "boundary_refutation_theorems": len({x for n in node_list if "boundary" in n["site_markers"]
                                                 for x in n["refutations_cited"]}),
            "qualified_failure_theorems": len({x for n in node_list if set(KIND_MARKER.values()) & set(n["site_markers"])
                                               for x in n["refutations_cited"]}),
            "own_proof_by_origin": {o: tally(lambda n, o=o: n["class"] == "named" and n["proof_status"] == "proved"
                                             and o in n["proof_origins"])
                                    for o in PROOF_ORIGINS if o != "unclassified"},
            "new_proof_marker": tally(lambda n: "new-proof" in n["site_markers"]),
            "uses_edges": sum(len(n["uses"]) for n in node_list),
            "uses_edges_reviewed": sum(u["reviewed"] for n in node_list for u in n["uses"]),
            "uses_edges_by_verdict": {v: sum(u.get("verdict") == v for n in node_list for u in n["uses"])
                                      for v in REVIEW_VERDICTS if v != "unclear"},
            "uses_edges_added_by_review": sum(u["via"] == "review" for n in node_list for u in n["uses"]),
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


def resolved(n: dict) -> bool:
    """Proved, or closed without a claim to prove (implied / explanatory); never cited-out-of-scope."""
    return n["proof_status"] == "proved" or n["statement_status"] in ("implied", "explanatory")


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
        "lemmas and claims are counted as proved (a reviewed ledger record in printed, corrected or restricted "
        "form, excluding any result downgraded to incomplete by a status override); prose claims, "
        "algorithms, definitions and source-gap candidates are outside that count.",
        "",
        "Dependencies (`uses`) are read from TeX cross-references inside each result and its proof. "
        f"{s['uses_edges_reviewed']} of {s['uses_edges']} edges are classified in `docs/graph/uses-review.json` "
        "by an AI critic and an independent AI verifier (not author-reviewed); only `proof-dependency` edges "
        "count below, while `definition`, `comparison` and `wrong-target` edges are context. "
        "A real dependency can still be cited without `\\ref`.",
        "",
    ]

    def open_uses(n):
        # implied and explanatory nodes do not block their dependants; cited-out-of-scope nodes do
        return [u for u in n["uses"] if is_dependency(u) and not resolved(nodes[u["id"]])]

    def status_word(n):
        st = n["statement_status"]
        return f"implied ({n['implied_variant']})" if st == "implied" else st

    def row(n, extra=""):
        issues = (" · " + ", ".join(n["issues"])) if n["issues"] else ""
        note = (" · COVERAGE note only, no statement entry" if n["coverage_rows"]
                and n["statement_status"] == "prose-claim" else "")
        if n["implied_by"]:
            note += " · by " + ", ".join(f"`{x.rsplit('.', 1)[-1]}`" for x in n["implied_by"])
        if n["decision_anchors"]:
            note += " · user decision " + ", ".join(n["decision_anchors"])
        if n["statement_status"] not in CLOSING_STATUSES and n["closing_rows"]:
            note += " · also " + ", ".join(f"{k} (COVERAGE.md:{', '.join(map(str, v))})"
                                           for k, v in n["closing_rows"].items())
        return f"- {node_title(n)} — {tex_cite(n)} · statement `{status_word(n)}`{issues}{note}{extra}"

    def row_only(r):
        what = (" · by " + ", ".join(f"`{x.rsplit('.', 1)[-1]}`" for x in r["entries"]) + f" ({r['variant']})"
                if r["entries"] else "")
        anchor = f" · user decision {r['anchor']}" if r["anchor"] else ""
        return f"- {r['item']} — `docs/COVERAGE.md:{r['line']}` · no inventory node{what}{anchor}"

    named_open = [n for n in data["nodes"] if n["class"] == "named" and n["proof_status"] != "proved"]
    lines += ["## Open numbered results", "",
              "Numbered theorems, lemmas and claims with no reviewed ledger record "
              "(including those whose printed form is refuted in Lean).", ""]
    lines += [row(n) for n in named_open] or ["- none"]
    lines.append("")

    todo = [n for n in data["nodes"] if n["proof_status"] != "proved" and n["statement_status"] not in CLOSING_STATUSES]
    ready = [n for n in todo if not open_uses(n)]
    blocked = [n for n in todo if open_uses(n)]
    lines += ["## Ready: open nodes whose proof dependencies are all proved, implied or explanatory", "",
              "Open numbered results and prose claims (remarks, displayed claims) whose every "
              "proof-dependency edge to another node is proved. Definitions, assumptions and algorithms "
              "are context, not blockers.", ""]
    for cls, title in (("named", "Numbered results"), ("prose", "Remarks and displayed claims")):
        part = [n for n in ready if n["class"] == cls]
        lines += [f"### {title} ({len(part)})", ""]
        lines += [row(n) for n in part] or ["- none"]
        lines.append("")
    lines += [f"### Blocked: some proof dependency is not proved ({len(blocked)})", ""]
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

    closing_text = {
        "implied": ("Implied by a proved entry (not separately proved)",
                    "A COVERAGE row headed **Implied by `X`**: the item follows from the named statement entry, "
                    "with that entry's suffix (an implication from a corrected or restricted entry does not "
                    "give the printed item). The implication itself is not a separate Lean statement. Never "
                    "counted as proved; does not block dependants."),
        "explanatory": ("Explanatory (no mathematical claim)",
                        "A COVERAGE row headed **Explanatory (no mathematical claim)**: attribution, comparison, "
                        "motivation or notation, reviewed as making no claim to prove. Never counted as proved; "
                        "does not block dependants."),
        "cited-out-of-scope": ("Cited results out of scope (user decision)",
                               "A COVERAGE row headed **Out of scope: cited result**, with a dated user-decision "
                               "anchor: a result the book cites from the literature without stating it precisely "
                               "about its own objects. Not proved, never counted as proved, and it still blocks "
                               "dependants. The whole monograph cannot be called complete while any of these "
                               "remain."),
    }
    for k in CLOSING_STATUSES:
        title, text = closing_text[k]
        part = [n for n in data["nodes"] if n["statement_status"] == k]
        extra_rows = [r for r in data["closing_rows_without_node"] if r["kind"] == k]
        lines += [f"## {title} ({len(part)} nodes, {len(extra_rows)} unlabelled rows)", "", text, ""]
        lines += [row(n) for n in part] + [row_only(r) for r in extra_rows] or ["- none"]
        lines.append("")

    ctx = s["context_items"]
    lines += ["## Other obligations outside the numbered-result count", "",
              f"- Prose nodes (remarks and displayed claims): {s['prose_nodes']}, of which "
              + ", ".join(f"{v} {k}" for k, v in s["prose_by_statement_status"].items() if v) + ".",
              f"- Algorithms: {ctx['algorithm']}; definitions: {ctx['definition']}; assumptions: "
              f"{ctx['assumption']} (context items, not nodes; edges to them are recorded but never block).",
              f"- Source-gap candidates in the inventory: {s['source_gap_candidates']} (see `docs/SOURCE-ISSUES.md`).",
              "- Unlabelled prose claims not listed in `docs/COVERAGE.md` are not tracked as nodes.",
              f"- Supporting-infrastructure COVERAGE rows (attached to no node, proving nothing by themselves): "
              f"{len(data['supporting_rows'])}.",
              ""]
    if data["warnings"]:
        lines += ["## Generator warnings", ""] + [f"- {w}" for w in data["warnings"]] + [""]
    return "\n".join(lines)


def g7_problems(data: dict) -> list:
    """Gate G7: every statement entry resolves to a reviewed status.

    Fails on a node whose only status is "Lean statement without a reviewed status record" (an entry on
    a remark or display that no COVERAGE row reviews) and on an entry that matches no inventory item."""
    out = [f"{n['id']} ({n['display_name']}): {UNRECORDED_SUB_REASON}: "
           + ", ".join(e["name"].rsplit(".", 1)[-1] for e in n["statement_entries"])
           for n in data["nodes"] if n.get("site_sub_reason") == UNRECORDED_SUB_REASON]
    out += [w for w in data["warnings"] if w.startswith("statement entry ") and "matches no inventory entry" in w]
    out += [w for w in data["warnings"] if w.startswith(REVIEW_PATH + ":")]
    return out


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
    g7 = g7_problems(data)
    if g7:
        print("G7 failed: statement entries without a reviewed status (attach them to a reviewed item or add a "
              "COVERAGE row), or a stale docs/graph/uses-review.json:\n  " + "\n  ".join(g7))
        return 1
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
    print(f"wrote {NODES_PATH} ({len(data['nodes'])} nodes, {s['uses_edges']} uses edges, {s['uses_edges_reviewed']} reviewed) and {NEXT_PATH}")
    print(f"named results counted as proved (ledger record, no downgrade override): {s['named_results_with_ledger_record']} of {s['named_results_in_inventory']}")
    for w in data["warnings"]:
        print("warning: " + w)
    return 0


if __name__ == "__main__":
    sys.exit(main())

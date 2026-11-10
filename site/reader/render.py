"""HTML pages: book text on the left, Lean on the right."""

from __future__ import annotations

import html
import json
import re
from datetime import datetime, timezone

from .book import Book, ENV_NAMES
from .graph import GitReader, gen_nodes
from .info import InfoPages
from .lean import ENTRY_ORDER, LABELS, MARKERS, REPO, LeanIndex, chip
from .tex import RESULT_KINDS, html_id, label_id

# Items that are never "proved": they get no status chip, only "cited by" links.
CONTEXT_KINDS = {"algorithm", "assumption", "definition"}

MATHJAX = "https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml-full.js"
ARXIV = "https://arxiv.org/abs/2610.41903v1"
TITLE = "Statistical Foundations of Reinforcement Learning"
SUBTITLE = "A Non-Asymptotic Perspective"
MAINTAINER_HANDLE = "aaradhyapandeycs"
MAINTAINER_URL = "https://github.com/aaradhyapandeycs"
REPO_DISPLAY = REPO.split("//", 1)[1]
# Plain authorship statement (no claim of human review).
AUTHORSHIP = ("The Lean formalization, its proofs, the reviews recorded in the ledgers and this website were "
              "produced with AI assistance (Claude, by Anthropic) under the direction of the maintainer, "
              f'<a href="{MAINTAINER_URL}">{MAINTAINER_HANDLE}</a> on GitHub. The book is by its authors, '
              "who do not endorse this formalization.")
ORIGIN_WORDS = {
    "source-proof": "Formalizes the book's proof.",
    "source-proof-repaired": "Formalizes the book's proof, with gaps repaired by this project",
    "own-proof:source-cites": "New proof by this project: the book cites this result from the literature.",
    "own-proof:source-omits": "New proof by this project: the book omits the proof.",
}
OURS = "proposed by this project; not confirmed by the authors"
SUPPORTING = "not separately counted for this item"


def esc(t: str) -> str:
    return html.escape(t, quote=False)


def attr(t: str) -> str:
    return html.escape(t, quote=True)


def inline_math(t: str) -> str:
    """Bibliography titles keep TeX math as $...$; MathJax here only reads \\(...\\)."""
    return re.sub(r"\$([^$]+)\$", r"\\(\1\\)", t)


def tex_text(raw: str, detex) -> str:
    """Bibliography field: prose parts de-TeXed and escaped, $...$ math kept verbatim for MathJax."""
    out = []
    for i, part in enumerate(re.split(r"(?<!\\)\$([^$]+)\$", raw)):
        if i % 2:
            out.append(f"\\({esc(part)}\\)")
        else:  # keep the spaces around math that the de-TeXer would trim
            pre, post = (" " if part[:1].isspace() else ""), (" " if part[-1:].isspace() else "")
            out.append(pre + esc(detex(part)) + post if part.strip() else part)
    return "".join(out)


def strip_tags(t: str) -> str:
    t = re.sub(r"<[^>]+>", "", t)
    return html.unescape(t)


class Site(InfoPages):
    def __init__(self, book: Book, lean: LeanIndex, pages: list, front: list, back: list,
                 ci_run_url: str | None = None, audit_line: str | None = None):
        self.book, self.lean, self.pages = book, lean, pages
        self.ci_run_url, self.audit_line = ci_run_url, audit_line
        self.where: dict = {}
        self.front, self.back = front, back
        self.built = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
        # Node graph from the ledgers at the same Lean revision (also used by the Status and
        # Graph pages), so the reader and the graph place and classify entries the same way.
        builder = gen_nodes.Builder(GitReader(lean.git))
        self.node_data = builder.build()
        for n in self.node_data["nodes"]:
            n["issues"] = list(n["issues"])
        self.nodes = {n["id"]: n for n in self.node_data["nodes"]}
        self.summary = self.node_data["summary"]
        self.label_node = {l: n for n in self.node_data["nodes"] for l in n["labels"]}
        self.entry_node = dict(builder.entry_node)
        self.inv_by_id = builder.by_id
        self.attach_unlabelled_rows()
        self.place()

    def attach_unlabelled_rows(self):
        """Coverage rows that gen_nodes attaches to a node by its number ("Remark 5.6, ...") rather than
        by a label: key them by the node id, so an unlabelled remark with only a ledger row (for example
        an implied or explanatory one) shows that row and its status instead of nothing."""
        by_line = {r["line"]: r for r in getattr(self.lean, "coverage_rows", [])}
        for n in self.node_data["nodes"]:
            if n["statement_entries"] or any(l in self.lean.coverage for l in n["labels"]):
                continue
            rows = [by_line[l] for l in n["coverage_rows"] if l in by_line]
            if rows:
                self.lean.coverage.setdefault("id:" + n["id"], []).extend(
                    {"item": r["item"], "evidence": r["evidence"], "scope": r["scope"]} for r in rows)

    # pairing -------------------------------------------------------------------
    def block_keys(self, b) -> set:
        keys = set(b.labels or [])
        if b.entry:
            keys.add("id:" + b.entry["id"])
            keys.update(b.entry.get("labels", []))
        return keys

    @staticmethod
    def units(b) -> list:
        """A top-level block followed by its nested numbered or labelled blocks."""
        return [b] + list(b.children)

    def primary_keys(self, e) -> set:
        """Keys of the one source item an entry formalizes: its ledger record's inventory entry,
        else the node gen_nodes attaches it to (label in the docstring's first range, else range)."""
        nid = self.entry_node.get(e.full)
        if not nid:
            return set()
        keys = {"id:" + nid}
        keys.update(self.inv_by_id.get(nid, {}).get("labels", []))
        return keys

    def place(self):
        """Show each Lean entry in full at the source item it formalizes (primary pass); only
        entries with no such item fall back to the first block they cite, in book order."""
        by_key: dict = {}
        ranged = []
        for e in self.lean.entries:
            keys = [l for l in e.labels if l in self.book.label_owner]
            rid = (e.record or {}).get("source_inventory_id")
            if rid:
                keys.append("id:" + rid)
            for k in keys:
                by_key.setdefault(k, []).append(e)
            if not keys:
                ranged.append(e)
        primary = {e.name: self.primary_keys(e) for e in self.lean.entries}
        self.matches: dict = {}  # id(block) -> [entries citing it]
        self.home: dict = {}     # id(block) -> [entries shown in full there]
        self.placed: dict = {}   # entry name -> (page id, anchor, id(top-level block), id(block))
        blocks = [(page, top, b) for page in self.pages for top in page.blocks for b in self.units(top)]

        def put(e, page, top, b):
            if e.name not in self.placed:
                self.placed[e.name] = (page.id, self.anchor(b), id(top), id(b))
                self.home.setdefault(id(b), []).append(e)
                self.matches.setdefault(id(b), [])
                if e not in self.matches[id(b)]:
                    self.matches[id(b)].append(e)

        # Primary pass. A display inside a paragraph carries its label only as an anchor in the
        # paragraph's HTML, so a block also matches when it holds the anchor of a primary label.
        needles = {e.name: [f'id="{label_id(k)}"' for k in sorted(primary[e.name]) if not k.startswith("id:")]
                   for e in self.lean.entries}
        for page, top, b in blocks:  # the block that is the item itself
            keys = self.block_keys(b)
            for e in self.lean.entries:
                if e.name not in self.placed and primary[e.name] & keys:
                    put(e, page, top, b)
        for page, top, b in blocks:  # else the block holding the item's anchor
            for e in self.lean.entries:
                if e.name not in self.placed and any(n in (b.html or "") for n in needles[e.name]):
                    put(e, page, top, b)
        for page, top, b in blocks:  # citations, and the first-cited fallback
            found = []
            for key in sorted(self.block_keys(b)):
                for e in by_key.get(key, []):
                    if e not in found:
                        found.append(e)
            if b.kind == "env" and b.file:
                for e in ranged:
                    for r in e.ranges:
                        if b.file.endswith(r["file"]) and r["line_start"] <= b.line_start <= r["line_end"] \
                                and e.name not in self.placed and e not in found:
                            found.append(e)
            if found:
                lst = self.matches.setdefault(id(b), [])
                for e in found:
                    if e not in lst:
                        lst.append(e)
                    put(e, page, top, b)
        self.unplaced = [e for e in self.lean.entries if e.name not in self.placed]

    @staticmethod
    def kind_of(b) -> str:
        return "algorithm" if b.kind == "algorithm" else (getattr(b, "kind_name", "") if b.kind == "env" else "")

    def placement_problems(self) -> list:
        """Build check: every named-ledger record's card sits at its own source item."""
        bad = []
        for e in self.lean.entries:
            if not e.record or e.name not in self.placed:
                continue
            want = set()
            if e.record.get("source_inventory_id"):
                want.add("id:" + e.record["source_inventory_id"])
            if e.record.get("source_label"):
                want.add(e.record["source_label"])
            b = next((b for p in self.pages for t in p.blocks for b in self.units(t)
                      if id(b) == self.placed[e.name][3]), None)
            if want and (b is None or not (want & self.block_keys(b))):
                bad.append(f"{e.name}: ledger item {sorted(want)} but shown at {self.placed[e.name][:2]}")
        return bad

    @staticmethod
    def anchor(b) -> str:
        if b.anchor:
            return b.anchor
        if b.labels:
            return label_id(b.labels[0])
        return ""

    # labels (all from the node graph) -----------------------------------------------
    def node_of_block(self, b):
        if b.entry and b.entry.get("id") in self.nodes:
            return self.nodes[b.entry["id"]]
        for l in b.labels or []:
            if l in self.label_node:
                return self.label_node[l]
        return None

    def statuses(self, b) -> list:
        """The reader label of the source item at this block ([] for algorithms, assumptions,
        definitions, explanatory items and blocks that are not nodes). Read from the node graph only."""
        if self.kind_of(b) in CONTEXT_KINDS:
            return []
        n = self.node_of_block(b)
        if n is None or not n.get("site_label"):
            # a block that only holds the anchor of a placed entry (a display inside a paragraph)
            for e in self.home.get(id(b), []):
                nn = self.nodes.get(self.entry_node.get(e.full, ""))
                if nn and nn.get("site_label"):
                    return [nn["site_label"]]
            return []
        return [n["site_label"]]

    def issue_html(self, n: dict) -> str:
        return self.lean.issue_links([c[1:] for c in n.get("issues", []) if c[1:] in self.lean.issue_slugs])

    def node_chip(self, n: dict, issues: bool = False) -> str:
        return chip(n.get("site_label"), n.get("site_markers", ()), n.get("site_sub_reason", ""),
                    self.issue_html(n) if issues else "")

    def item_header(self, n: dict) -> str:
        """The item's one label (the same one the results index and the graph show), its markers and,
        for a refuted printed statement, the refutation theorems."""
        refuted = ""
        pr = n.get("printed_refuted") or {}
        what = ("A corrected or restricted form is proved instead (below)." if n["proof_status"] == "proved"
                else "Part of the item is proved (below); the item is not counted as proved."
                if n["statement_status"] == "partial" else "Nothing is proved for the printed statement.")
        reading = self.lean.md(pr["reading"]) if pr.get("reading") else "see the coverage ledger"
        if "refuted" in n.get("site_markers", ()):
            names = ", ".join(f'<code title="{attr(x)}">{esc(x.rsplit(".", 1)[-1])}</code>'
                              for x in (pr.get("lean") or n["refutations_cited"])) or "see the coverage ledger"
            more = (" Some further failures are paper arguments by this project, not checked in Lean."
                    if pr.get("paper") else "")
            refuted = (f'<p class="refuted-line tex2jax_process"><strong>Refuted in Lean</strong> under this reading: '
                       f'{reading} Lean: {names}.{more} {what} The refutation and any correction are {OURS}.</p>')
        elif "boundary" in n.get("site_markers", ()):
            names = ", ".join(f'<code title="{attr(x)}">{esc(x.rsplit(".", 1)[-1])}</code>'
                              for x in (pr.get("lean") or n["refutations_cited"])) or "see the coverage ledger"
            more = (" Some further boundary cases are paper arguments by this project, not checked in Lean."
                    if pr.get("paper") else "")
            refuted = (f'<p class="refuted-line boundary tex2jax_process"><strong>Fails at a boundary case '
                       f'(checked in Lean):</strong> {reading} Lean: {names}.{more} Only a degenerate boundary or '
                       f'domain case fails; the repair restricts the domain. {what} The finding and any correction '
                       f'are {OURS}.</p>')
        elif "fails-paper" in n.get("site_markers", ()):
            refuted = (f'<p class="refuted-line paper tex2jax_process"><strong>Appears to fail (paper argument, not '
                       f'checked in Lean):</strong> {reading} {what} The argument and any correction are {OURS}.</p>')
        return (f'<div class="item-status"><span class="item-name">{esc(n["display_name"])}</span>'
                f'{self.node_chip(n, issues=True)}{refuted}</div>')

    def entry_label(self, e):
        """(label, markers, sub-reason) of one statement entry, from its node and ledger record."""
        n = self.nodes.get(self.entry_node.get(e.full, ""))
        if n is None:
            return "incomplete", [], "statement entry not attached to a tracked item"
        se = next((x for x in n["statement_entries"] if x["name"] == e.full), None)
        variant = se["variant"] if se else None
        to_label = {"printed": "stated", "corrected": "corrected", "restricted": "restricted"}
        rec = e.record or {}
        if rec.get("status_override"):
            # The entry itself is proved; it is shown as a related result, not as the printed item.
            return "incomplete", [], "this entry: a related result, not counted for the printed item"
        # The entry's status follows the node graph's `counted` flag (one rule for card and nodes.json).
        if not (se and se.get("counted")):
            if n["class"] == "prose" and n["statement_status"] == "partial":
                return "incomplete", [], "Note, not a status: partial result toward this item (not counted as proved)"
            if n["class"] == "prose" and n["proof_status"] != "proved":
                return "incomplete", [], n.get("site_sub_reason") or "not counted as proved"
            return "supporting", [], SUPPORTING
        if n["proof_status"] != "proved" or e.status == "partial" or variant not in to_label:
            return "incomplete", [], n.get("site_sub_reason") or "partial"
        label = to_label[variant]
        markers = []
        if label == "restricted" and "corrected" in e.name.lower():
            markers.append("also-corrected")
        if (rec.get("proof_origin") or "").startswith("own-proof"):
            markers.append("new-proof")
        return label, markers, ""

    def audit_link(self, e) -> str:
        if not hasattr(self, "_audit_files"):
            self._audit_files = {}
            for f in self.lean.git.ls("docs/statement-audit"):
                try:
                    self._audit_files[f] = self.lean.git.show(f)
                except RuntimeError:
                    pass
        for f, text in sorted(self._audit_files.items()):
            if f.endswith("README.md"):
                continue
            if re.search(r"(?<![\w])%s(?![\w])" % re.escape(e.name), text):
                return (f'<a href="{attr(self.lean.git.blob(f))}">statement audit '
                        f'({esc(f.rsplit("/", 1)[-1])})</a>')
        readme = "docs/statement-audit/README.md"
        if readme in self._audit_files:
            return f'<a href="{attr(self.lean.git.blob(readme))}">statement audit (method)</a>'
        return ""

    def entry_view(self, e) -> dict:
        label, markers, sub = self.entry_label(e)
        n = self.nodes.get(self.entry_node.get(e.full, ""), {})
        rec = e.record or {}
        note = next((d["note"] for d in n.get("display_notes", []) if d["entry"] == e.full), "")
        view = {"label": label, "markers": markers, "sub": sub, "note": note, "audit": self.audit_link(e)}
        if n.get("tex"):
            t = n["tex"][0]
            view["tex"] = f'<span class="texref">TeX <code>{esc(t["file"].rsplit("/", 1)[-1])}:{t["line_start"]}–{t["line_end"]}</code></span>'
        if label in ("corrected", "restricted") and (n.get("correction_status") or "proposed-by-project") != "author-confirmed":
            word = "Correction" if (label == "corrected" or "also-corrected" in markers) else "Restriction"
            view["correction"] = f"{word} {OURS}."
        origin = rec.get("proof_origin")
        if origin in ORIGIN_WORDS:
            text = esc(ORIGIN_WORDS[origin])
            if origin == "source-proof-repaired":
                text += f" ({self.lean.issue_links(e.issues)})." if e.issues else "."
            if rec.get("status_override") and origin.startswith("own-proof"):
                # the proof is of the related result shown here, not of the printed theorem
                text = ("New proof (of the related result above, not of the printed theorem) by this project; "
                        + ("the book cites the printed result from the literature."
                           if origin == "own-proof:source-cites" else "the book omits the proof."))
                text = esc(text)
            view["origin"] = text
        cov = f'<a href="{attr(self.lean.git.blob("docs/COVERAGE.md"))}">coverage ledger</a>'
        if not rec:
            if sub == SUPPORTING:
                view["explain"] = ("A supporting Lean statement for this result. The numbered-result ledger has no "
                                   "record for it, so it is not counted as a proof of the item.")
            elif label == "incomplete" and n.get("statement_status") == "partial":
                view["explain"] = (f"This entry proves part of the item. The {cov} records the item as partial, so "
                                   "it is not counted as proved.")
            elif label != "incomplete":
                view["explain"] = (f"Status from the reviewed {cov} row for this item (remarks and displayed "
                                   "claims are reviewed there, not in the numbered-result ledger).")
            if not note:
                row = self.coverage_row_for(e, n)
                if row:
                    view["cov_note"] = row["scope"]
        if label in ("corrected", "restricted") and not e.issues:
            # the item's source issues (a display entry's docstring may not repeat them), else its disclosure
            view["node_issues"] = [c[1:] for c in n.get("issues", []) if c[1:] in self.lean.issue_slugs]
            if not view["node_issues"]:
                view["disclosure"] = self.lean.disclosure_for(e)
        return view

    def coverage_row_for(self, e, n):
        """The COVERAGE row that names this entry (backticked), else the node's first reviewed row."""
        rows = getattr(self.lean, "coverage_rows", [])
        pat = re.compile(r"`(?:[\w.']*\.)?%s`" % re.escape(e.name))
        named = [r for r in rows if pat.search(r["scope"])]
        if named:
            return named[0]
        lines = set(n.get("coverage_rows", []))
        return next((r for r in rows if r["line"] in lines and gen_nodes.closing_kind(r["lead"]) is None), None)

    def card(self, e) -> str:
        return self.lean.card(e, self.entry_view(e))

    def lean_column(self, page, top) -> str:
        return self.lean_columns(page, top)[0]

    def lean_columns(self, page, top) -> tuple:
        """(cards beside the block, cards in a row of their own right after it). A card whose item is
        a display inside an algorithm (or another context item) is not shown beside the algorithm:
        the algorithm gets a link, and the card follows the algorithm in its own row."""
        out, after, seen, ledger_seen = [], [], set(), set()
        cites = []
        context = self.kind_of(top) in CONTEXT_KINDS
        for b in self.units(top):
            entries = self.matches.get(id(b), [])
            home = self.home.get(id(b), [])
            n = self.node_of_block(b) if self.kind_of(b) not in CONTEXT_KINDS else None
            if n is None and home:
                n = self.nodes.get(self.entry_node.get(home[0].full, ""))
            sink = after if context else out
            own_cards, other_cards = [], []
            for e in sorted(entries, key=lambda e: (e not in home, ENTRY_ORDER.index(e.status))):
                if e.name in seen:
                    continue
                seen.add(e.name)
                pid, _, top_id, _ = self.placed[e.name]
                if pid == page.id and top_id == id(top):
                    lab = self.entry_label(e)[0]
                    best = n.get("site_label") if n else None
                    (own_cards if lab == best or not best else other_cards).append(self.card(e))
                    if context:
                        out.append(f'<div class="lean-ref">The Lean entry <a href="#lean-{attr(e.name)}"><code>'
                                   f'{esc(e.name)}</code></a> formalizes {esc(self.where_label(e))} inside this '
                                   f'{esc(ENV_NAMES.get(self.kind_of(top), self.kind_of(top)).lower())}; it is shown '
                                   f'right after it.</div>')
                else:
                    cites.append(f'<a href="{pid}.html#lean-{attr(e.name)}"><code>{esc(e.name)}</code></a> '
                                 f'(at {esc(self.where_label(e))})')
            if not own_cards and other_cards:
                own_cards, other_cards = other_cards, []
            if own_cards or other_cards:
                if n:
                    sink.append(self.item_header(n))
                sink.extend(own_cards)
                if other_cards:
                    sink.append(f'<details class="other-entries"><summary>Other Lean entries for this item '
                                f'({len(other_cards)})</summary>{"".join(other_cards)}</details>')
            if not home:
                keys = sorted(l for l in (b.labels or []) if l in self.lean.coverage)
                if b.entry and "id:" + b.entry["id"] in self.lean.coverage:
                    keys.append("id:" + b.entry["id"])
                for lab in keys:
                    if lab in ledger_seen:
                        continue
                    ledger_seen.add(lab)
                    ln = self.nodes.get(lab[3:]) if lab.startswith("id:") else self.label_node.get(lab)
                    if ln is None:
                        owner = self.book.label_owner.get(lab)
                        ln = self.nodes.get(owner["id"]) if owner else None
                    if ln is not None and self.kind_of(b) in CONTEXT_KINDS:
                        ln = None
                    shown = ln["display_name"] if ln else lab
                    view = ({"label": ln.get("site_label"), "markers": ln.get("site_markers", ()),
                             "sub": ln.get("site_sub_reason", "")} if ln else
                            {"label": None, "markers": (), "sub": "ledger note (not a tracked item)"})
                    if ln and {"refuted", "boundary"} & set(ln.get("site_markers", ())):
                        out.append(self.item_header(ln))
                        view = {"label": None, "markers": (), "sub": ""}  # shown once, in the header
                    out.append(self.lean.ledger_card(shown, self.lean.coverage[lab], view))
            own_keys = set(b.labels or []) | ({"id:" + b.entry["id"]} if b.entry else set())
            if not home and not (own_keys & ledger_seen) and b.kind == "env" \
                    and getattr(b, "kind_name", "") in RESULT_KINDS | {"remark"} and n is not None:
                out.append(f'<div class="lean-none">{self.node_chip(n)}'
                           f'{(" " + esc(n["display_name"])) if b is not top else ""}</div>')
        if cites:
            word = "entry" if len(cites) == 1 else "entries"
            out.append(f'<div class="lean-ref">Also cited by the Lean {word} {", ".join(cites)}, shown with '
                       f'{"its own item" if len(cites) == 1 else "their own items"}.</div>')
        return "".join(out), "".join(after)

    def where_label(self, e) -> str:
        nid = self.entry_node.get(e.full)
        inv = self.inv_by_id.get(nid or "", {})
        kind = inv.get("kind", "")
        if kind in ("display", "subequations"):
            num = inv.get("number") or next((r.get("number") for r in inv.get("rows", []) if r.get("number")), None)
            return f"display ({num})" if num else "its display"
        if inv.get("number"):
            return f"{ENV_NAMES.get(kind, kind.capitalize())} {inv['number']}"
        return "its own row"

    # page pieces -----------------------------------------------------------------
    def block_html(self, b) -> str:
        h = b.html
        if b.kind in ("env", "algorithm") and b.tex and b.file:
            fname = b.file.split("/tex/", 1)[-1]
            h += (f'<details class="tex-src"><summary>TeX source · {esc(fname)}:{b.line_start}–{b.line_end}</summary>'
                  f'<pre>{esc(b.tex)}</pre></details>')
        if b.in_proof:
            h = f'<div class="in-proof">{h}</div>'
        return h

    def page_body(self, page) -> str:
        rows, buf = [], []

        def flush():
            if buf:
                rows.append(f'<div class="row"><div class="book-col">{"".join(buf)}</div>'
                            f'<aside class="lean-col" aria-hidden="true"></aside></div>')
                buf.clear()

        for b in page.blocks:
            col, after = self.lean_columns(page, b)
            if col:
                flush()
                rows.append(f'<div class="row paired"><div class="book-col">{self.block_html(b)}</div>'
                            f'<aside class="lean-col" aria-label="Lean">{col}</aside></div>')
                if after:
                    rows.append(f'<div class="row paired lean-after"><div class="book-col"></div>'
                                f'<aside class="lean-col" aria-label="Lean">{after}</aside></div>')
            else:
                buf.append(self.block_html(b))
        flush()
        return "".join(rows)

    def toc(self, current: str | None) -> str:
        chapters, cur_ch = [], None
        current_page = next((p for p in self.pages if p.id == current), None)
        for p in self.pages:
            if p.level == 0:
                cur_ch = {"page": p, "sections": []}
                chapters.append(cur_ch)
            elif cur_ch:
                cur_ch["sections"].append(p)
        out = ['<nav class="toc" aria-label="Book contents"><a class="toc-home" href="book.html">Contents</a><ol>']
        for ch in chapters:
            p = ch["page"]
            is_open = current_page is not None and current_page.chapter == p.chapter
            items = "".join(
                f'<li><a href="{s.id}.html"{" aria-current=page" if s.id == current else ""}>'
                f'<span class="secnum">{esc(s.number or "")}</span> {s.title}</a></li>' for s in ch["sections"])
            out.append(f'<li><details{" open" if is_open else ""}><summary><a href="{p.id}.html"'
                       f'{" aria-current=page" if p.id == current else ""}><span class="secnum">{esc(p.number or "")}</span> '
                       f'{p.title}</a></summary><ol>{items}</ol></details></li>')
        out.append('<li class="toc-extra"><a href="acknowledgements.html">Acknowledgements</a></li>')
        out.append('<li class="toc-extra"><a href="references.html">References</a></li></ol></nav>')
        return "".join(out)

    NAV = [("index", "Overview"), ("results", "Results"), ("book", "Book"), ("graph", "Dependency graph"),
           ("status", "Progress", [("status", "Counts by chapter"), ("errata", "Source issues")]),
           ("methodology", "Methodology"), ("contribute", "Contribute"), ("credits", "Credits")]

    def nav_html(self, current: str | None, mobile: bool = False) -> str:
        cur = current or ""
        book_ids = {p.id for p in self.pages} | {"book", "acknowledgements", "references"}
        out = []
        for item in self.NAV:
            pid, word = item[0], item[1]
            here = (cur == pid or (pid == "book" and cur in book_ids)
                    or (len(item) > 2 and cur in {x[0] for x in item[2]}))
            mark = ' aria-current="page"' if here else ""
            if len(item) > 2:
                subs = "".join(f'<a href="{x}.html"{" aria-current=page" if cur == x else ""}>{w}</a>' for x, w in item[2])
                if mobile:
                    out.append(f'<span class="menu-group">{word}</span>{subs}')
                else:
                    out.append(f'<details class="dd"><summary{mark}>{word}</summary><div class="dd-menu">{subs}</div></details>')
            else:
                out.append(f'<a href="{pid}.html"{mark}>{word}</a>')
        out.append(f'<a href="{REPO}">GitHub ↗</a>')
        return "".join(out)

    def shell(self, title: str, body: str, current: str | None = None, toc: bool = True) -> str:
        rev = self.lean.git.rev
        layout = (f'<div class="layout">{self.toc(current)}<main id="main">{body}</main></div>' if toc
                  else f'<div class="layout single"><main id="main">{body}</main></div>')
        toc_btn = '<button class="toc-toggle" type="button" aria-label="Show book contents">Contents</button>' if toc else ""
        return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(title)}</title>
<link rel="stylesheet" href="assets/style.css">
<script src="assets/theme.js"></script>
<script>{self.inline_mathjax_config()}</script>
<script defer src="{MATHJAX}"></script>
</head>
<body class="tex2jax_ignore{" has-toc" if toc else ""}">
<a class="skip" href="#main">Skip to content</a>
<header class="top">
  {toc_btn}<a class="brand" href="index.html">Statistical Foundations of RL <span>in Lean</span></a>
  <nav class="links" aria-label="Site">{self.nav_html(current)}</nav>
  <details class="menu"><summary aria-label="Menu">Menu</summary><nav class="menu-links" aria-label="Site">{self.nav_html(current, True)}</nav></details>
  <button class="theme" type="button" aria-label="Switch between light and dark">◐</button>
</header>
<div class="banner"><strong>Incomplete formalization.</strong> Statuses come from the project ledgers at commit
<code>{rev[:7]}</code>; reviews are by AI agents, not refereed or author-approved. <a href="methodology.html">Methodology</a></div>
{layout}
<footer>
<p>Book text: {esc(self.authors_text())}, <em>{TITLE}: {SUBTITLE}</em>, <a href="{ARXIV}">arXiv:2610.41903v1</a>,
licensed <a href="https://creativecommons.org/licenses/by/4.0/">CC BY 4.0</a>. Changes were made: converted from
the pinned TeX to HTML, comments and author-only material removed, math typeset by MathJax. The authors do not
endorse this formalization. Lean code: Apache-2.0, commit <a href="{REPO}/tree/{rev}"><code>{rev[:10]}</code></a>
(<a href="{REPO}/commit/{rev}">CI status for this commit</a>), Lean <code>{esc(self.toolchain())}</code>, Mathlib
<code>{esc(self.mathlib_rev()[:10])}</code>. Built {self.built}. <a href="credits.html">Credits</a> ·
<a href="methodology.html#verify">Check it yourself</a></p>
</footer>
<script src="assets/app.js"></script>
</body>
</html>
"""

    # pages ----------------------------------------------------------------------
    def book_pages(self) -> dict:
        out = {}
        for i, page in enumerate(self.pages):
            prev_ = self.pages[i - 1] if i else None
            next_ = self.pages[i + 1] if i + 1 < len(self.pages) else None
            nav = '<nav class="pager">'
            if prev_:
                nav += f'<a class="prev" href="{prev_.id}.html">← {esc(prev_.number or "")} {prev_.title}</a>'
            if next_:
                nav += f'<a class="next" href="{next_.id}.html">{esc(next_.number or "")} {next_.title} →</a>'
            nav += "</nav>"
            head = ('<div class="cols-head"><span>Book text</span><span>Lean</span></div>')
            body = head + self.page_body(page) + nav
            title = f"{page.number + ' ' if page.number else ''}{strip_tags(page.title)} · {TITLE}"
            out[page.id] = self.shell(title, body, page.id)
        return out

    # counts: every number shown comes from the node-graph summary ------------------------
    def count_value(self, path: str):
        v = self.summary
        for k in path.split("."):
            v = v[k]
        return v

    def cnt(self, path: str) -> str:
        """A count from `summary` (dotted path), tagged so build.py can check it against nodes.json."""
        return f'<span class="n" data-count="{attr(path)}">{self.count_value(path)}</span>'

    def cntw(self, path: str, one: str, many: str) -> str:
        """A tagged count followed by the singular or plural noun phrase."""
        return f'{self.cnt(path)} {one if self.count_value(path) == 1 else many}'

    def label_counts(self, prefix: str, with_zero: bool = False) -> str:
        parts = []
        for k in gen_nodes.SITE_LABEL_ORDER:
            if with_zero or self.count_value(f"{prefix}.{k}"):
                parts.append(f'{self.cnt(f"{prefix}.{k}")} <span class="status {LABELS[k][1]}">{esc(LABELS[k][0])}</span>')
        return ", ".join(parts)

    def count_sentence(self) -> str:
        return (f'Of the {self.cnt("named_results_in_inventory")} numbered theorems, lemmas and claims: '
                f'{self.label_counts("named_by_label", True)}. Of these, {self.cnt("named_refuted_marker")} have '
                f'a printed statement refuted in Lean under the reading formalized, marked '
                f'<span class="marker mk-refuted">{esc(MARKERS["refuted"])}</span>; '
                f'{self.cnt("named_boundary_marker")} more fail in Lean only at a degenerate boundary case '
                f'(the domain is repaired), marked <span class="marker mk-boundary">{esc(MARKERS["boundary"])}</span>, and '
                f'{self.cnt("named_fails_paper_marker")} more appear to fail by a paper argument of this project '
                f'(not checked in Lean), marked <span class="marker mk-fails-paper">{esc(MARKERS["fails-paper"])}'
                f'</span>. Remarks and displayed claims are counted separately ({self.cnt("prose_nodes")} tracked): '
                f'{self.label_counts("prose_by_label")}; {self.cnt("prose_by_label.no_claim")} make no '
                f'mathematical claim and carry no label. Algorithms, definitions and assumptions carry no label. '
                f'These are counts, not a percentage of the book.')

    # anchors and links ---------------------------------------------------------------
    def index_anchors(self, html_pages: dict):
        for pid, text in html_pages.items():
            for m in re.finditer(r'id="([^"]+)"', text):
                self.where.setdefault(html.unescape(m.group(1)), pid)

    def href(self, n: dict) -> str | None:
        for a in [label_id(l) for l in n.get("labels", [])] + ["E-" + html_id(n["id"])]:
            if a in self.where:
                return f"{self.where[a]}.html#{a}"
        # An unlabelled display with no anchor of its own: link the first of its Lean cards.
        for se in n.get("statement_entries", []):
            a = "lean-" + se["name"].rsplit(".", 1)[-1]
            if a in self.where:
                return f"{self.where[a]}.html#{a}"
        return None

    def block_titles(self) -> dict:
        """Rendered titles of the book's blocks by inventory id (the converter's own HTML, citations
        and math included), so titles read as in the book."""
        if not hasattr(self, "_titles"):
            self._titles = {}
            for page in self.pages:
                for top in page.blocks:
                    for b in self.units(top):
                        if b.entry and getattr(b, "title", None):
                            self._titles.setdefault(b.entry["id"], b.title)
        return self._titles

    def title_html(self, n: dict) -> str:
        t = self.block_titles().get(n.get("id", ""), "")
        return f'<span class="tex2jax_process">{t}</span>' if t else ""

    def chapter_pages(self) -> list:
        return [p for p in self.pages if p.level == 0]

    def chapter_title(self, ch) -> str:
        p = next((p for p in self.pages if p.level == 0 and p.chapter == ch), None)
        return p.title if p else ""

    # results index ---------------------------------------------------------------------
    def result_rows(self) -> list:
        """One row per node of the node graph (numbered results, remarks, displays) and per context item
        (algorithm, definition, assumption), in book order. Labels come from the nodes only."""
        order = {k: i for i, k in enumerate(self.inv_by_id)}
        items = [("node", n) for n in self.node_data["nodes"]] + [("context", c) for c in self.node_data["context"]]
        items.sort(key=lambda x: order.get(x[1]["id"], 10 ** 9))
        rows = []
        for cls, n in items:
            name = n.get("display_name") or gen_nodes.display_name(n)
            rows.append({"id": n["id"], "name": name, "kind": n["kind"], "chapter": n.get("chapter") or "",
                         "class": n.get("class", "context"), "label": n.get("site_label"),
                         "markers": list(n.get("site_markers", [])), "sub": n.get("site_sub_reason", ""),
                         "tex_label": (n.get("labels") or [""])[0],
                         "title": strip_tags(self.block_titles().get(n["id"], "")),
                         "lean": [e["name"].rsplit(".", 1)[-1] for e in n.get("statement_entries", [])],
                         "issues": n.get("issues", []), "href": self.href(n)})
        return rows

    def results_page(self) -> str:
        rows = self.result_rows()
        trs, last_ch = [], None
        for r in rows:
            if r["chapter"] != last_ch:
                last_ch = r["chapter"]
                trs.append(f'<tr class="ch-row" data-ch="{attr(last_ch)}"><th colspan="4">Chapter {esc(last_ch)} '
                           f'{self.chapter_title(last_ch)}</th></tr>')
            n = self.nodes.get(r["id"]) or self.inv_by_id.get(r["id"], {})
            st = (self.node_chip(self.nodes[r["id"]], issues=True) if r["id"] in self.nodes
                  else '<span class="entry-note">Context item (not a status): no label</span>')
            name = esc(r["name"])
            name = f'<a href="{attr(r["href"])}">{name}</a>' if r["href"] else name
            lean = " ".join(f'<code>{esc(x)}</code>' for x in r["lean"])
            lean_cell = (f'<details class="lean-list"><summary>{len(r["lean"])} entr{"y" if len(r["lean"]) == 1 else "ies"}'
                         f'</summary>{lean}</details>' if len(r["lean"]) > 1 else lean) or "—"
            search = " ".join([r["name"], r["title"], r["tex_label"], *r["lean"], *r["issues"]]).lower()
            title = self.title_html(self.inv_by_id.get(r["id"], {}))
            trs.append(f'<tr data-label="{attr(r["label"] or "none")}" data-markers="{attr(" ".join(r["markers"]))}" '
                       f'data-ch="{attr(r["chapter"])}" data-named="{1 if r["class"] == "named" else 0}" '
                       f'data-search="{attr(search)}" id="r-{attr(html_id(r["id"]))}">'
                       f'<td data-th="Item">{name}</td>'
                       f'<td data-th="{"Title" if title else "Label"}">{title}<div class="label"><code>{esc(r["tex_label"])}</code></div></td>'
                       f'<td data-th="Status">{st}</td><td data-th="Lean" class="lean-names">{lean_cell}</td></tr>')
        chips = "".join(f'<button type="button" class="chip" data-filter="{k}" aria-pressed="false">'
                        f'<span class="status {LABELS[k][1]}">{esc(LABELS[k][0])}</span></button>'
                        for k in gen_nodes.SITE_LABEL_ORDER)
        chapters = "".join(f'<option value="{attr(p.chapter)}">Chapter {esc(p.chapter)}</option>'
                           for p in self.chapter_pages() if p.chapter)
        unplaced = ""
        if self.unplaced:
            items = "".join(f'<li>{chip(*self.entry_label(e))} '
                            f'<a href="{attr(self.lean.git.blob(e.file, e.line_start, e.line_end))}"><code>{esc(e.name)}</code></a></li>'
                            for e in self.unplaced)
            unplaced = ('<section class="unplaced"><h2>Lean entries not matched to a book location</h2>'
                        "<p>These statement-index entries cite no label or line range that the reader could match. "
                        f"They are listed so nothing is hidden.</p><ul>{items}</ul></section>")
        body = f"""<h1>Results</h1>
<p class="lede">Every source item the project tracks, in book order: the numbered theorems, lemmas and claims,
the remarks and displayed claims, and (with no label) the algorithms, definitions and assumptions. Each label is
read from the node graph generated from the project's ledgers at commit <code>{self.lean.git.rev[:10]}</code>.
The counts by label are on <a href="status.html">Progress</a>. The TeX label under each title is shown exactly as written in the
book's source, including any misspelling.</p>
<div class="filters" role="search"><input type="search" id="q" placeholder="Search number, title, label, Lean name or C-id" aria-label="Search results">
<div class="chips" role="group" aria-label="Filter by label"><button type="button" class="chip on" data-filter="" aria-pressed="true">All</button>{chips}
<label class="toggle"><input type="checkbox" id="f-refuted"> <span class="marker mk-refuted">{esc(MARKERS["refuted"])}</span></label>
<label class="toggle"><input type="checkbox" id="f-boundary"> <span class="marker mk-boundary">{esc(MARKERS["boundary"])}</span></label>
<label class="toggle"><input type="checkbox" id="f-paper"> <span class="marker mk-fails-paper">{esc(MARKERS["fails-paper"])}</span></label>
<label class="toggle"><input type="checkbox" id="f-new"> <span class="marker mk-new-proof">{esc(MARKERS["new-proof"])}</span></label>
<label class="toggle"><input type="checkbox" id="f-named" checked> numbered results only</label>
<select id="f-ch" aria-label="Chapter"><option value="">All chapters</option>{chapters}</select></div>
<p class="filter-count" aria-live="polite"></p></div>
<div class="table-wrap"><table class="results stack"><thead><tr><th>Item</th><th>Title and label</th><th>Status</th><th>Lean entries</th></tr></thead>
<tbody>{''.join(trs)}</tbody></table></div>{unplaced}"""
        return self.shell(f"Results · {TITLE}", body, "results", toc=False)

    # overview ---------------------------------------------------------------------------
    def stacked_bar(self) -> str:
        total = self.count_value("named_results_in_inventory") or 1
        segs = []
        for k in gen_nodes.SITE_LABEL_ORDER:
            v = self.count_value(f"named_by_label.{k}")
            if v:
                segs.append(f'<span class="seg seg-{k}" style="width:{100 * v / total:.3f}%" '
                            f'title="{v} {attr(LABELS[k][0])}"></span>')
        legend = "".join(f'<li><span class="sw seg-{k}"></span>{self.cnt(f"named_by_label.{k}")} '
                         f'{esc(LABELS[k][0])}</li>' for k in gen_nodes.SITE_LABEL_ORDER)
        return (f'<div class="bar" role="img" aria-label="Labels of the numbered results">{"".join(segs)}</div>'
                f'<ul class="bar-legend">{legend}</ul>')

    def snapshot_line(self) -> str:
        rev = self.lean.git.rev
        return (f'Ledgers and Lean at commit <a href="{REPO}/tree/{rev}"><code>{rev[:10]}</code></a> · '
                f'Lean <code>{esc(self.toolchain())}</code> · Mathlib <code>{esc(self.mathlib_rev()[:10])}</code> · '
                f'built {esc(self.built)}')

    def node_list(self, ns: list) -> str:
        items = []
        for n in ns:
            link = self.href(n)
            name = esc(n["display_name"])
            items.append(f'<li><a href="{attr(link)}">{name}</a>' if link else f"<li>{name}")
            items[-1] += f' {self.node_chip(n)}</li>'
        return f'<ul class="node-list">{"".join(items)}</ul>' if items else "<p>None.</p>"

    def index_page(self) -> str:
        front = "".join(b.html for b in self.front)
        chapters = self.chapter_pages()
        theorems = [n for n in self.node_data["nodes"] if n["class"] == "named" and n["kind"] == "theorem"]
        main, last = [], None
        for n in theorems:
            if n["chapter"] != last:
                last = n["chapter"]
                main.append(f'<tr class="ch-row"><th colspan="3">Chapter {esc(last)} {self.chapter_title(last)}</th></tr>')
            link = self.href(n)
            name = f'<a href="{attr(link)}">{esc(n["display_name"])}</a>' if link else esc(n["display_name"])
            main.append(f'<tr><td data-th="Result">{name}</td><td data-th="Title">{self.title_html(n)}</td>'
                        f'<td data-th="Status">{self.node_chip(n)}</td></tr>')
        lis = []
        for ch in chapters:
            c = self.summary["by_chapter"].get(ch.chapter or "", {})
            if c.get("named_total"):
                bits = ", ".join(f'{self.cnt(f"by_chapter.{ch.chapter}.named_by_label.{k}")} {esc(LABELS[k][0])}'
                                 for k in gen_nodes.SITE_LABEL_ORDER if c["named_by_label"][k])
                summary = f'{bits} (of {self.cnt(f"by_chapter.{ch.chapter}.named_total")} numbered results)'
            else:
                summary = "no numbered results"
            lis.append(f'<li><a href="{ch.id}.html"><span class="secnum">{esc(ch.number or "")}</span> {ch.title}</a>'
                       f'<span class="ch-count">{summary}</span></li>')
        new = self.whats_new()
        body = f"""<section class="hero">
<h1>{TITLE}<span>{SUBTITLE}</span></h1>
<p class="authors">{esc(self.authors_text())} · <a href="{ARXIV}">arXiv:2610.41903v1</a></p>
<p>The monograph, rendered from its pinned arXiv TeX source, with a Lean&nbsp;4 formalization shown next to the
results it covers. Each result links to its exact <code>.tex</code> lines and to the Lean source at a fixed commit.
This formalization is <strong>not complete</strong>, it is <strong>not endorsed by the authors</strong>, and its
reviews were done by AI agents, <strong>not by a human referee</strong>.</p>
<p class="actions"><a class="button primary" href="book.html">Read the book</a>
<a class="button" href="#main-results">Main results</a> <a class="button" href="methodology.html">Methodology</a></p>
</section>
{self.explainer()}
<section><h2>At a glance</h2>
<p class="lede">The {self.cnt("named_results_in_inventory")} numbered theorems, lemmas and claims, by label:</p>
{self.stacked_bar()}
<p class="bar-caption">This bar counts only the {self.cnt("named_results_in_inventory")} numbered results. It is
<strong>not a completion percentage</strong>: algorithms, definitions, assumptions, remarks and displayed claims are
tracked separately, and the corrected and restricted segments are variants of the printed statement, not the printed
statement itself. All counts are on <a href="status.html">Progress</a>.</p>
<p>{self.cntw("named_refuted_marker", "numbered result", "numbered results")} and {self.cntw("prose_refuted_marker", "remark or display", "remarks or displays")}
have a printed statement refuted in Lean under the reading formalized
(<a href="results.html#m=refuted&amp;all=1">show them</a>); {self.cntw("named_boundary_marker", "numbered result", "numbered results")} and
{self.cntw("prose_boundary_marker", "remark or display", "remarks or displays")} fail in Lean only at a degenerate boundary case, with the
domain repaired (<a href="results.html#m=boundary&amp;all=1">show them</a>); {self.cntw("named_fails_paper_marker", "numbered result", "numbered results")} and
{self.cntw("prose_fails_paper_marker", "remark or display", "remarks or displays")} appear to fail by a paper argument of this project, not
checked in Lean (<a href="results.html#m=fails-paper&amp;all=1">show them</a>). Remarks and displayed claims
({self.cnt("prose_nodes")} tracked): {self.label_counts("prose_by_label")}; {self.cnt("prose_by_label.no_claim")}
make no mathematical claim. <a href="status.html">Progress by chapter</a>.</p>
<p class="snapshot">{self.snapshot_line()}</p></section>
<section id="main-results"><h2>Main results</h2>
<p class="lede">Every numbered theorem of the book, generated from the node graph (no hand selection). Lemmas,
claims, remarks and displays are in the <a href="results.html">results index</a>.</p>
<div class="table-wrap"><table class="results stack main-results"><thead><tr><th>Result</th><th>Title</th><th>Status</th></tr></thead>
<tbody>{"".join(main)}</tbody></table></div></section>
{new}
<section><h2>How to read this site</h2>
<ul class="legend">
<li><span class="status st-stated">proved as stated</span> the Lean statement is the printed result, and the reviewed ledger records it as proved.</li>
<li><span class="status st-corrected">proved with corrections</span> a corrected form is proved; the card says what differs from the print and links the source issue.</li>
<li><span class="status st-restricted">proved under restrictions</span> a special case of the printed result is proved; the card states the restriction.</li>
<li><span class="status st-incomplete">incomplete</span> nothing counted as proved for the printed item yet (the small text says why).</li>
<li><span class="marker mk-refuted">{esc(MARKERS["refuted"])}</span> Lean proves the printed statement false under the reading formalized.</li>
<li><span class="marker mk-boundary">{esc(MARKERS["boundary"])}</span> Lean shows the printed statement fails only at a degenerate boundary or domain case (for example T = 1, where a formula divides by log T = 0, or a single action); a domain restriction repairs it. Not counted as refuted.</li>
<li><span class="marker mk-fails-paper">{esc(MARKERS["fails-paper"])}</span> a paper argument by this project (not checked in Lean) shows the printed statement fails.</li>
</ul>
<p>On a book page the book text is on the left and the Lean card on the right (below it on narrow screens). The
card shows what is proved first; the Lean statement, its proof and the library theorems are in closed
disclosures. Every card links its <code>.tex</code> lines and the pinned Lean lines. <a href="methodology.html#labels">Full legend</a>.</p></section>
<section><h2>Chapters</h2><ol class="chapters">{''.join(lis)}</ol></section>
<section class="abstract"><details><summary><h2>Abstract of the book (by the authors)</h2></summary>{front}</details></section>"""
        return self.shell(TITLE, body, "index", toc=False)

    def explainer(self) -> str:
        return ('''<section class="explain" id="what-is-lean"><h2>What does “proved in Lean” mean here?</h2>
<p><strong>Lean</strong> is a proof assistant: a statement and its proof are written in full detail, and a small
trusted program, the kernel, checks every inference step. Nothing is accepted on the strength of an argument that
“looks right”.</p>
<p><strong>Proved in Lean</strong> on this site means that a formal statement, written by this project from the
book’s text, was checked by the kernel, using only Lean’s logic, the Mathlib library and three standard axioms
(<code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code>).</p>
<p>It does <strong>not</strong> mean that the authors approved the formal statement, and it does not by itself show
that the formal statement is what the book means. That match is checked by AI review (not by a human referee), and
the authors can judge it by reading the statement beside the book text. When the formal statement differs from the
printed one, the label says so.</p>
<p>Technical terms are explained in the <a href="methodology.html#glossary">glossary</a>.</p></section>''')

    def whats_new(self) -> str:
        named = [n for n in self.node_data["nodes"] if n["class"] == "named"]
        own = [n for n in named if any(o.startswith("own-proof") for o in n.get("proof_origins", []))]
        repaired = [n for n in named if "source-proof-repaired" in n.get("proof_origins", [])]
        corrected = [n for n in named if n.get("site_label") == "corrected"
                     or "also-corrected" in n.get("site_markers", ())]
        refuted = [n for n in self.node_data["nodes"] if "refuted" in n.get("site_markers", ())]
        classified = any(n.get("proof_origins") for n in named)
        own_html = (f'<p>{self.cnt("own_proof_by_origin.own-proof:source-cites")} numbered results whose proof the book '
                    f'cites from the literature and {self.cnt("own_proof_by_origin.own-proof:source-omits")} whose proof '
                    f'the book omits have a new proof here; {self.cnt("own_proof_by_origin.source-proof-repaired")} follow '
                    f'the book\'s proof with gaps repaired.</p><h4>New proofs</h4>{self.node_list(own)}'
                    f'<h4>The book\'s proof, with gaps repaired</h4>{self.node_list([n for n in repaired if n not in own])}'
                    if classified else
                    '<p>The ledger does not yet record, for each result, whether the Lean proof follows the book\'s '
                    'argument or is new; until it does, no result is marked “new proof”.</p>')
        return f"""<section id="new"><h2>What is new here</h2>
<p class="lede">Everything in this section is {OURS}.</p>
<h3>New proofs and repaired proofs</h3>{own_html}
<h3>Proposed corrections</h3>
<p>Numbered results proved only in a corrected form (the printed statement needs a change):</p>
{self.node_list(corrected)}
<h3>Machine-checked counterexamples</h3>
<p>{self.cnt("refutation_theorems")} Lean theorems refute a printed statement, under the reading formalized, for
these {self.cnt("refuted_marker_nodes")} items. A refutation is only as good as the reading; each card states it.</p>
{self.node_list(refuted)}
<h3>Boundary cases (domain repaired)</h3>
<p>For these {self.cnt("boundary_marker_nodes")} items, {self.cnt("boundary_refutation_theorems")} Lean theorems show
that the printed statement fails only at a degenerate boundary or domain case (for example T = 1, where the printed
schedule divides by log T = 0, or a single action, where every policy is optimal). Adding the missing domain condition
repairs it; these are not counted as refutations.</p>
{self.node_list([n for n in self.node_data["nodes"] if "boundary" in n.get("site_markers", ())])}
<h3>Failures shown by a paper argument only</h3>
<p>For these {self.cnt("fails_paper_marker_nodes")} items a paper argument by this project (not checked in Lean)
shows that the printed statement fails; each card states the case.</p>
{self.node_list([n for n in self.node_data["nodes"] if "fails-paper" in n.get("site_markers", ())])}
<p><a href="errata.html">All source issues</a>.</p></section>"""

    def bibtex_book(self) -> str:
        p = self.book.provenance
        aid = p.get("arxiv_id", "2610.41903v1")
        return ("@misc{chen2026statistical,\n"
                f"  title         = {{{p.get('title', TITLE + ': ' + SUBTITLE)}}},\n"
                f"  author        = {{{' and '.join(p.get('authors', []))}}},\n"
                "  year          = {2026},\n"
                f"  eprint        = {{{aid.split('v')[0]}}},\n"
                "  archivePrefix = {arXiv},\n"
                f"  note          = {{Version {aid}}},\n"
                f"  url           = {{https://arxiv.org/abs/{aid}}}\n}}")

    def bibtex_repo(self) -> str:
        rev = self.lean.git.rev
        return ("@software{statistical_foundations_rl_lean,\n"
                "  title  = {Statistical Foundations of Reinforcement Learning in Lean: an incomplete\n"
                "            Lean 4 formalization of arXiv:2610.41903v1},\n"
                f"  author = {{{MAINTAINER_HANDLE} (maintainer)}},\n"

                f"  url    = {{{REPO}}},\n"
                f"  note   = {{Commit {rev}; built {self.built}. Produced with AI assistance (Claude, by\n"
                f"            Anthropic) under the direction of the maintainer}}\n}}")

    def references_page(self) -> str:
        items = []
        keys = sorted(self.book.cited, key=lambda k: (self.book.authors(k)[0].lower(), self.book.authors(k)[1]))
        for k in keys:
            e = self.book.bib.get(k)
            if not e:
                items.append(f'<li id="ref-{attr(k)}"><code>{esc(k)}</code> (not in the bibliography file)</li>')
                continue
            d = self.book.detex
            venue = d(e.get("journal") or e.get("booktitle") or e.get("publisher") or e.get("howpublished") or "")
            items.append(f'<li id="ref-{attr(k)}">{esc(d(e.get("author", "")).replace(" and ", ", "))}. '
                         f'<em>{tex_text(e.get("title", ""), d)}</em>. {inline_math(esc(venue))}'
                         f'{", " if venue else ""}{esc(d(e.get("year", "")))}.</li>')
        body = f"<h1>References</h1><ol class=\"refs tex2jax_process\">{''.join(items)}</ol>"
        return self.shell(f"References · {TITLE}", body, "references")

    def ack_page(self) -> str:
        body = "<h1>Acknowledgements</h1>" + "".join(b.html for b in self.back)
        return self.shell(f"Acknowledgements · {TITLE}", body, "acknowledgements")

    # references between pages ----------------------------------------------------
    def resolve(self, pages: dict) -> dict:
        where = {}
        for pid, text in pages.items():
            for m in re.finditer(r'id="([^"]+)"', text):
                where.setdefault(html.unescape(m.group(1)), pid)
        missing = {}

        def fmt(mode, cmd, label):
            num, kind = self.book.label_number(label)
            if num is None:
                missing[label] = missing.get(label, 0) + 1
                return "??"
            text = f"({num})" if cmd == "eqref" or (cmd in ("cref", "Cref") and kind == "equation") else num
            if cmd in ("cref", "Cref"):
                word = {"equation": "Eq.", "heading": "Section", "display": "Eq."}.get(kind, ENV_NAMES.get(kind, kind.capitalize()))
                text = f"{word} {text}"
            if mode == "m":
                return text
            anchor = label_id(label)
            pid = where.get(anchor)
            if not pid:
                owner = self.book.label_owner.get(label)
                if owner and ("E-" + html_id(owner["id"])) in where:
                    anchor = "E-" + html_id(owner["id"])
                    pid = where[anchor]
            if not pid:
                return esc(text)
            return f'<a class="ref" href="{pid}.html#{attr(anchor)}">{esc(text)}</a>'

        out = {}
        for pid, text in pages.items():
            out[pid] = re.sub(r"@@REF\|(\w)\|(\w+)\|([^@]*)@@", lambda m: fmt(m.group(1), m.group(2), m.group(3)), text)
        self.missing_refs = missing
        # a reference inside a page title becomes plain text (no markup in <title>)
        for pid in out:
            out[pid] = re.sub(r"<title>(.*?)</title>",
                              lambda m: "<title>" + esc(strip_tags(m.group(1))) + "</title>", out[pid], count=1, flags=re.S)
        return out

    def inline_mathjax_config(self) -> str:
        """The configuration inlined in every page, so the book's macros are defined even
        when `assets/` is not reachable (a saved page, a snapshot preview); identical to
        `assets/mathjax-config.js`."""
        if not hasattr(self, "_mathjax_inline"):
            self._mathjax_inline = self.mathjax_config().replace("</", "<\\/")
        return self._mathjax_inline

    def mathjax_config(self) -> str:
        macros = self.book.mathjax_macros()
        cfg = {
            "tex": {"packages": {"[+]": ["mathtools", "boldsymbol", "color", "html", "cancel", "textmacros"]},
                    "macros": macros, "tags": "none", "processEscapes": True, "processEnvironments": True,
                    "inlineMath": [["\\(", "\\)"]], "displayMath": [["\\[", "\\]"]]},
            "options": {"ignoreHtmlClass": "tex2jax_ignore", "processHtmlClass": "tex2jax_process"},
            "chtml": {"scale": 1.0},
        }
        return "window.MathJax = " + json.dumps(cfg, ensure_ascii=False, indent=1) + ";\n"

    def search_data(self) -> str:
        return json.dumps(self.result_rows(), ensure_ascii=False)

    # verification facts read from the pinned revision ---------------------------------
    def toolchain(self) -> str:
        return self.lean.git.show("lean-toolchain").strip()

    def mathlib_rev(self) -> str:
        m = json.loads(self.lean.git.show("lake-manifest.json"))
        return next(p["rev"] for p in m["packages"] if p["name"] == "mathlib")

    def authors_text(self) -> str:
        a = self.book.provenance.get("authors") or []
        return ", ".join(a[:-1]) + " and " + a[-1] if len(a) > 1 else "".join(a)

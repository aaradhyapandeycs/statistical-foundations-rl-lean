"""HTML pages: book text on the left, Lean on the right."""

from __future__ import annotations

import html
import json
import re
from datetime import datetime, timezone

from .book import Book, ENV_NAMES
from .graph import GitReader, gen_nodes
from .lean import (PROVED, REFUTED_READING, REPO, RESTRICTED_COUNT_NOTE, STATUS, STATUS_ORDER, LeanIndex,
                   coverage_status)
from .tex import RESULT_KINDS, label_id

# Items that are never "proved": they get no status chip, only "cited by" links.
CONTEXT_KINDS = {"algorithm", "assumption", "definition"}

MATHJAX = "https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml-full.js"
ARXIV = "https://arxiv.org/abs/2610.41903v1"
TITLE = "Statistical Foundations of Reinforcement Learning"
SUBTITLE = "A Non-Asymptotic Perspective"
AUTHORS = "Yuxin Chen, Yuejie Chi, Jianqing Fan, Gen Li, Yuting Wei and Yuling Yan"
MAINTAINER_HANDLE = "aaradhyapandeycs"
MAINTAINER_URL = "https://github.com/aaradhyapandeycs"
REPO_DISPLAY = REPO.split("//", 1)[1]
# Plain authorship statement shown on the home and About pages (no claim of human review).
AUTHORSHIP = ("The Lean formalization, its proofs, the reviews recorded in the ledgers and this website were "
              "produced with AI assistance (Claude, by Anthropic) under the direction of the maintainer, "
              f'<a href="{MAINTAINER_URL}">{MAINTAINER_HANDLE}</a> on GitHub. The book is by its six authors, '
              "who do not endorse this formalization.")


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


class Site:
    def __init__(self, book: Book, lean: LeanIndex, pages: list, front: list, back: list):
        self.book, self.lean, self.pages = book, lean, pages
        self.front, self.back = front, back
        self.built = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
        # Node graph from the ledgers at the same Lean revision (also used by the Status and
        # Graph pages), so the reader and the graph place and classify entries the same way.
        builder = gen_nodes.Builder(GitReader(lean.git))
        self.node_data = builder.build()
        for n in self.node_data["nodes"]:
            n["issues"] = list(n["issues"])
        self.nodes = {n["id"]: n for n in self.node_data["nodes"]}
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

    def statuses(self, b) -> list:
        """Statuses of the entries shown at this block. Algorithms, assumptions and definitions
        get none: an entry that cites them does not make them "proved"."""
        if self.kind_of(b) in CONTEXT_KINDS:
            return []
        sts = [e.status for e in self.home.get(id(b), [])]
        if not sts:
            for lab in self.block_keys(b):
                for row in self.lean.coverage.get(lab, []):
                    sts.append(coverage_status(row["scope"]))
        return sorted(set(sts), key=STATUS_ORDER.index)

    def refutation_note(self, b) -> str:
        """For a result proved only in some other form whose printed statement Lean refutes."""
        n = self.nodes.get((b.entry or {}).get("id", ""))
        if not n or not n["refutations_cited"] or n["proof_status"] != "proved":
            return ""
        names = ", ".join(f"<code>{esc(x)}</code>" for x in n["refutations_cited"])
        issues = self.lean.issue_links([c[1:] for c in n["issues"] if c[1:] in self.lean.issue_slugs])
        return (f'<div class="refuted-note"><strong>Printed statement refuted in Lean</strong> ({names}). '
                f'The card below proves a {"corrected" if n["statement_status"] == "corrected" else "restricted"} '
                f'form, not the printed statement.{(" " + issues) if issues else ""}</div>')

    def lean_column(self, page, top) -> str:
        return self.lean_columns(page, top)[0]

    def lean_columns(self, page, top) -> tuple:
        """(cards beside the block, cards in a row of their own right after it). A card whose item is
        a display inside an algorithm (or another context item) is not shown beside the algorithm:
        the algorithm gets a link, and the card follows the algorithm in its own row."""
        out, after, seen, ledger_seen = [], [], set(), set()
        context = self.kind_of(top) in CONTEXT_KINDS
        for b in self.units(top):
            entries = self.matches.get(id(b), [])
            home = self.home.get(id(b), [])
            if home:
                out.append(self.refutation_note(b))
            for e in sorted(entries, key=lambda e: (e not in home, STATUS_ORDER.index(e.status))):
                if e.name in seen:
                    continue
                seen.add(e.name)
                pid, _, top_id, _ = self.placed[e.name]
                if pid == page.id and top_id == id(top) and context:
                    after.append(self.lean.card(e))
                    out.append(f'<div class="lean-ref">The Lean entry <a href="#lean-{attr(e.name)}"><code>'
                               f'{esc(e.name)}</code></a> formalizes {esc(self.where_label(e))} inside this '
                               f'{esc(ENV_NAMES.get(self.kind_of(top), self.kind_of(top)).lower())}; it is shown '
                               f'right after it.</div>')
                elif pid == page.id and top_id == id(top):
                    out.append(self.lean.card(e))
                else:
                    where = self.where_label(e)
                    out.append(f'<div class="lean-ref">Cited by the Lean entry '
                               f'<a href="{pid}.html#lean-{attr(e.name)}"><code>{esc(e.name)}</code></a>, '
                               f'shown at {esc(where)}. Its status there: {esc(STATUS[e.status][0].lower())}.</div>')
            entries = home
            if not entries:
                keys = sorted(l for l in (b.labels or []) if l in self.lean.coverage)
                if b.entry and "id:" + b.entry["id"] in self.lean.coverage:
                    keys.append("id:" + b.entry["id"])
                for lab in keys:
                    if lab not in ledger_seen:
                        ledger_seen.add(lab)
                        shown = gen_nodes.node_title(self.nodes[lab[3:]]) if lab.startswith("id:") else lab
                        out.append(self.lean.ledger_card(shown, self.lean.coverage[lab]))
            if not entries and not (set(b.labels or []) & ledger_seen) and b.kind == "env" \
                    and getattr(b, "kind_name", "") in RESULT_KINDS:
                word, cls = STATUS["none"]
                name = f'{ENV_NAMES.get(b.kind_name, "")} {b.number or ""}'.strip() if b is not top else ""
                out.append(f'<div class="lean-none"><span class="status {cls}">{esc(word)}</span>'
                           f'{(" " + esc(name)) if name else ""}</div>')
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
        out = ['<nav class="toc" aria-label="Book contents"><a class="toc-home" href="index.html">Contents</a><ol>']
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

    def shell(self, title: str, body: str, current: str | None = None, toc: bool = True) -> str:
        nav = [("index.html", "Home"), ("results.html", "Results"), ("status.html", "Status"),
               ("graph.html", "Graph"), ("errata.html", "Source issues"), ("about.html", "About")]
        links = "".join(f'<a href="{h}"{" aria-current=page" if h == (current or "") + ".html" else ""}>{t}</a>'
                        for h, t in nav)
        layout = (f'<div class="layout">{self.toc(current)}<main id="main">{body}</main></div>' if toc
                  else f'<div class="layout single"><main id="main">{body}</main></div>')
        return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(title)}</title>
<link rel="stylesheet" href="assets/style.css">
<script src="assets/theme.js"></script>
<script src="assets/mathjax-config.js"></script>
<script defer src="{MATHJAX}"></script>
</head>
<body class="tex2jax_ignore">
<a class="skip" href="#main">Skip to content</a>
<header class="top">
  <button class="toc-toggle" type="button" aria-label="Show contents">☰</button>
  <a class="brand" href="index.html">Statistical Foundations of RL <span>in Lean</span></a>
  <nav class="links">{links}<a href="{ARXIV}">arXiv ↗</a><a href="{REPO}/tree/{self.lean.git.rev}">GitHub ↗</a>
  <button class="theme" type="button" aria-label="Switch between light and dark">◐</button></nav>
</header>
<div class="banner">This formalization is <strong>incomplete</strong>. A status shows what the project's ledger
records for one Lean entry; it never certifies a chapter or the book. Ledger reviews are independent reviews by AI
agents against the pinned TeX; no result has been refereed by a human mathematician or approved by the authors.
<a href="about.html#status">How status works</a> · <a href="about.html#verify">Check it yourself</a>.</div>
{layout}
<footer>
<p>Book text: {AUTHORS}, <em>{TITLE}: {SUBTITLE}</em>, <a href="{ARXIV}">arXiv:2610.41903v1</a>,
licensed <a href="https://creativecommons.org/licenses/by/4.0/">CC BY 4.0</a>. Changes were made: converted from
the pinned TeX to HTML, comments and author-only material removed, math typeset by MathJax. The authors do not
endorse this formalization. Lean code: Apache-2.0, commit <a href="{REPO}/tree/{self.lean.git.rev}"><code>{self.lean.git.rev[:10]}</code></a>
(<a href="{REPO}/commit/{self.lean.git.rev}">Lean CI status for this commit</a>). Built {self.built}.</p>
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

    def result_rows(self) -> list:
        rows = []
        for page in self.pages:
            for top in page.blocks:
                for b in self.units(top):
                    kind = getattr(b, "kind_name", None) if b.kind == "env" else ("algorithm" if b.kind == "algorithm" else None)
                    paired = id(b) in self.home
                    if not kind and not paired:
                        continue
                    sts = self.statuses(b)
                    if not sts and kind in RESULT_KINDS:
                        sts = ["none"]
                    label = b.labels[0] if b.labels else ""
                    name = ENV_NAMES.get(kind, "Algorithm" if kind == "algorithm" else "Display") if kind else "Display"
                    rows.append({"page": page.id, "anchor": self.anchor(b), "chapter": page.chapter,
                                 "section": page.number or "", "kind": name, "number": b.number or "",
                                 "title": strip_tags(b.title or ""), "label": label, "statuses": sts,
                                 "lean": [e.name for e in self.home.get(id(b), [])],
                                 "result": kind in RESULT_KINDS})
        return rows

    def results_page(self) -> str:
        rows = self.result_rows()
        chips = "".join(f'<button type="button" class="chip" data-filter="{s}"><span class="status {STATUS[s][1]}">'
                        f'{esc(STATUS[s][0])}</span></button>' for s in STATUS_ORDER)
        trs, last_ch = [], None
        for r in rows:
            if r["chapter"] != last_ch:
                last_ch = r["chapter"]
                ch = next((p for p in self.pages if p.level == 0 and p.chapter == last_ch), None)
                trs.append(f'<tr class="ch-row"><th colspan="4">{esc(last_ch or "")} {ch.title if ch else ""}</th></tr>')
            st = "".join(f'<span class="status {STATUS[s][1]}">{esc(STATUS[s][0])}</span>' for s in r["statuses"])
            lean = " ".join(f'<code>{esc(n)}</code>' for n in r["lean"])
            search = " ".join([r["kind"], r["number"], r["title"], r["label"], *r["lean"]]).lower()
            trs.append(f'<tr data-status="{" ".join(r["statuses"]) or "other"}" data-search="{attr(search)}">'
                       f'<td><a href="{r["page"]}.html#{attr(r["anchor"])}">{esc(r["kind"])} {esc(r["number"])}</a></td>'
                       f'<td>{esc(r["title"])}<div class="label"><code>{esc(r["label"])}</code></div></td>'
                       f'<td>{st}</td><td class="lean-names">{lean}</td></tr>')
        unplaced = ""
        if self.unplaced:
            items = "".join(f'<li><span class="status {STATUS[e.status][1]}">{esc(STATUS[e.status][0])}</span> '
                            f'<a href="{attr(self.lean.git.blob(e.file, e.line_start, e.line_end))}"><code>{esc(e.name)}</code></a></li>'
                            for e in self.unplaced)
            unplaced = ('<section class="unplaced"><h2>Lean entries not matched to a book location</h2>'
                        "<p>These statement-index entries cite no label or line range that the reader could match. "
                        f"They are listed so nothing is hidden.</p><ul>{items}</ul></section>")
        counts = self.counts()
        body = f"""<h1>Results</h1>
<p class="lede">Every numbered theorem, lemma, corollary, proposition, claim, definition, assumption, remark,
example and algorithm of the book, in book order, plus displayed equations that a Lean entry cites. The
status column is derived from the project's reviewed ledger at commit <code>{self.lean.git.rev[:10]}</code>.
{counts}</p>
<div class="filters"><input type="search" id="q" placeholder="Search number, title, label or Lean name" aria-label="Search results">
<div class="chips"><button type="button" class="chip on" data-filter="">All</button>{chips}</div></div>
<div class="table-wrap"><table class="results"><thead><tr><th>Item</th><th>Title and label</th><th>Status</th><th>Lean entries</th></tr></thead>
<tbody>{''.join(trs)}</tbody></table></div>{unplaced}"""
        return self.shell(f"Results · {TITLE}", body, "results", toc=False)

    def counts(self) -> str:
        rows = [r for r in self.result_rows() if r["result"]]
        total = len(rows)
        by = {s: 0 for s in STATUS_ORDER}
        for r in rows:
            by[r["statuses"][0] if r["statuses"] else "none"] += 1
        refuted = [f'{r["kind"]} {r["number"]}' for r in rows if r["statuses"] and r["statuses"][0] == "refuted"]
        words = {"original": "proved as printed", "corrected": "proved in corrected form",
                 "restricted": "proved for a restricted case", "unrecorded": "with a statement entry but no reviewed status",
                 "partial": "partial",
                 "implied": "implied by a proved entry (not counted as proved)",
                 "explanatory": "explanatory only (no claim)",
                 "cited-out-of-scope": "cited from the literature and not formalized here (project scope decision; not proved)",
                 "refuted": f"refuted in Lean under the reading formalized ({', '.join(refuted)}), nothing proved",
                 "ledger": "with a ledger note only", "none": "not yet formalized"}
        parts = [f"{by[s]} {words.get(s, STATUS[s][0].lower())}" for s in STATUS_ORDER if by[s]]
        return (f"Of the {total} numbered theorems, lemmas, corollaries, propositions and claims, "
                + ", ".join(parts) + " (best status per item). Prose claims, algorithms and unlabelled"
                " displays are not in this count." + self.restricted_note(by["restricted"]))

    def restricted_note(self, n_restricted: int) -> str:
        notes = [t for name, t in RESTRICTED_COUNT_NOTE.items()
                 if any(e.name == name and e.status == "restricted" for e in self.lean.entries)]
        return f" Of the {n_restricted} restricted, " + " ".join(notes) if notes and n_restricted else ""

    def index_page(self) -> str:
        front = "".join(b.html for b in self.front)
        chapters = [p for p in self.pages if p.level == 0]
        rows = self.result_rows()
        lis = []
        for ch in chapters:
            rs = [r for r in rows if r["chapter"] == ch.chapter and r["result"]]
            best = [r["statuses"][0] if r["statuses"] else "none" for r in rs]
            bits = [f"{best.count(k)} {w}" for k, w in (("original", "proved as printed"),
                    ("corrected", "corrected form"), ("restricted", "restricted case")) if best.count(k)]
            summary = ((", ".join(bits) + f" of {len(rs)} results") if bits else
                       f"none of {len(rs)} results proved yet" if rs else "no numbered results")
            lis.append(f'<li><a href="{ch.id}.html"><span class="secnum">{esc(ch.number or "")}</span> {ch.title}</a>'
                       f'<span class="ch-count">{summary}</span></li>')
        body = f"""<section class="hero">
<h1>{TITLE}<span>{SUBTITLE}</span></h1>
<p class="authors">{AUTHORS} · <a href="{ARXIV}">arXiv:2610.41903v1</a></p>
<p>The whole monograph, rendered from its pinned arXiv TeX source, with Lean&nbsp;4 statements and proofs shown
next to the results they formalize. Each result links to its exact <code>.tex</code> lines and to the Lean source
at a fixed commit. Every status comes from the project's ledgers. Many prose claims, algorithms, remarks and
displays are not yet formalized, and the page says so where they appear. Reviews recorded in the ledgers are
independent reviews by AI agents against the pinned TeX; no result has been refereed by a human mathematician or
approved by the authors.</p>
<p class="authorship">{AUTHORSHIP}</p>
<p class="stats">{self.counts()}</p>
<p class="actions"><a class="button primary" href="{chapters[0].id if chapters else 'index'}.html">Read the book →</a>
<a class="button" href="results.html">Browse results</a>
<a class="button" href="errata.html">Source issues (candidates)</a> <a class="button" href="about.html#verify">Check it yourself</a></p>
</section>
<section class="abstract"><h2>Abstract of the book (by the authors)</h2>{front}</section>
<section><h2>Chapters</h2><ol class="chapters">{''.join(lis)}</ol></section>"""
        return self.shell(TITLE, body, "index", toc=False)

    def about_page(self) -> str:
        legend = "".join(f'<li><span class="status {STATUS[s][1]}">{esc(STATUS[s][0])}</span> {esc(desc)}</li>'
                         for s, desc in [
                             ("original", "The named-result ledger records the printed result as proved: an independent AI-agent source review, a compiled Lean export and only the permitted axioms."),
                             ("corrected", "A corrected variant is proved; the card says what differs and links the source issue."),
                             ("restricted", "A restricted variant (for example positive sample sizes, or a smaller class of sets or algorithms) is proved; the card states the restriction. A result that is both corrected and restricted is counted as restricted."),
                             ("cov-printed", "A prose claim, remark, display or reading aid with no numbered-result record; the coverage ledger row that names it records it as proved as stated (or in corrected or restricted form, shown the same way)."),
                             ("unrecorded", "A statement entry exists in Lean but no ledger records it as proved, so it is not shown as proved."),
                             ("partial", "The coverage ledger lists components, but no statement entry covers the whole result."),
                             ("refuted", "Lean proves the printed statement false under the reading formalized (the card names the reading), and no corrected version is proved yet."),
                             ("implied", "The coverage ledger records that a named, proved statement entry implies this item; the implication is not a separate Lean statement, it carries the entry's corrected or restricted form, and it is never counted as proved."),
                             ("explanatory", "The coverage ledger records the item as attribution, comparison, motivation or notation with no mathematical claim; nothing is proved and it is never counted as proved."),
                             ("cited-out-of-scope", "A result the book cites from the literature; not formalized in this project (project scope decision, 2026-11-09). It is not proved, is never counted as proved, and keeps the formalization incomplete."),
                             ("ledger", "The coverage ledger has a note (for example a source gap or proposed repair); nothing is claimed as proved."),
                             ("none", "No Lean entry and no ledger note. This is the default.")])
        rev = self.lean.git.rev
        body = f"""<h1>About this reader</h1>
<p>This site shows <em>{TITLE}</em> (arXiv:2610.41903v1) next to the Lean&nbsp;4 formalization in
<a href="{self.lean.git.blob('README.md')}">statistical-foundations-rl-lean</a>. It was inspired by Axiom's
<a href="https://stacks.axiommath.ai/">Stacks Project in Lean</a> site and shares no code with it.</p>
<h2 id="status">How status works</h2>
<p>The site derives each status from the named-result ledger <code>docs/named-result-status.json</code> and the
coverage ledger <code>docs/COVERAGE.md</code> at commit <code>{rev[:10]}</code>. It never infers a proof from the
existence of Lean code. Corrected and restricted results are never shown as plain proofs. No chapter or the book
is described as complete.</p>
<p><strong>Who reviewed what.</strong> Lean checking is mechanical: a compiled export with only the axioms
<code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code> is the only machine guarantee.
Whether a Lean statement matches the printed result is judged by independent reviews performed by AI agents
against the pinned TeX, recorded in the ledgers. No result has been refereed by a human mathematician or approved
by the authors. Source issues (C1, C2, …) are candidates found by those reviews, not errors confirmed by the
authors. Cards with a named-result ledger record link the review record, so the reasoning can be checked.</p>
<p><strong>Who made this.</strong> {AUTHORSHIP} If we have misread the book, please tell us by opening an issue at
<a href="{REPO}/issues">{REPO_DISPLAY}/issues</a>.</p>
<p>A Lean card sits next to the source item it formalizes. When an entry also cites an algorithm, assumption,
definition or display, that item shows a “cited by” link instead of a card, and never a status of its own.</p>
<ul class="legend">{legend}</ul>
<h2>Sources</h2>
<ul>
<li>Book: the pinned arXiv source, restored and checked against SHA-256 hashes by <code>scripts/fetch_source.py</code>
(source archive {esc(self.book.provenance['artifacts']['2610.41903v1.tar'][:12])}…). The site follows the
<code>StatisticalRL-nowplain.tex</code> variant, so material marked arXiv-only is omitted.</li>
<li>Numbering, labels and line ranges: <code>docs/source-inventory.json</code>, a lexical checklist that certifies nothing.</li>
<li>Lean: statement-index entries in <code>Formalization/Statements/ChN.lean</code>, matched by the source labels and
<code>.tex</code> ranges cited in their docstrings; their <code>_holds</code> proofs; and the library theorems
named by the ledger. All read from commit <code>{rev}</code>.</li>
</ul>
<h2>Rendering</h2>
<p>A small converter turns the TeX into HTML and leaves the math to MathJax&nbsp;3, with the book's own macros.
Equation numbers come from the inventory. Each theorem-like block has a “TeX source” disclosure with its exact
lines, so the rendering can be checked against the source. PDF figures were converted to PNG. Figure numbers are computed by the reader (per chapter, as in the <code>book</code> class the publisher's class loads), because the inventory does not record them.</p>
<h2 id="verify">Check it yourself</h2>
<p>This site was built from commit <a href="{REPO}/tree/{rev}"><code>{rev}</code></a>
(<a href="{REPO}/commit/{rev}">its CI checks</a>; <a href="{REPO}/actions/workflows/lean.yml?query=branch%3Amain">Lean
CI runs on main</a>). The Lean toolchain and Mathlib version are pinned in
<a href="{self.lean.git.blob('lean-toolchain')}"><code>lean-toolchain</code></a> and
<a href="{self.lean.git.blob('lake-manifest.json')}"><code>lake-manifest.json</code></a>. To rebuild everything and
audit the axioms:</p>
<pre class="cite">git clone {REPO}.git
cd statistical-foundations-rl-lean
git checkout {rev}
lake exe cache get        # prebuilt Mathlib
lake build                # compiles every Lean file of the formalization
lake env lean Audit.lean  # transitive axiom audit of every StatisticalRL declaration</pre>
<p>Expected: the build succeeds with no <code>sorry</code>, and <a href="{self.lean.git.blob('Audit.lean')}"><code>Audit.lean</code></a>
prints “Axiom audit passed for N project declarations.” It collects the transitive axioms of every declaration in
the <code>StatisticalRL</code> namespace and fails on any axiom other than <code>propext</code>,
<code>Classical.choice</code> and <code>Quot.sound</code>. A statement is then checked
by reading its entry in <code>Formalization/Statements/ChN.lean</code> (each card links it) against the TeX
shown beside it.</p>
<h2 id="cite">How to cite</h2>
<p>The book:</p>
<pre class="cite">{esc(self.bibtex_book())}</pre>
<p>This formalization (incomplete; cite the commit you used):</p>
<pre class="cite">{esc(self.bibtex_repo())}</pre>
<h2>Licences</h2>
<p>As in the page footer: book text and figures CC BY 4.0, attributed to the six authors (changes as described
above; the authors do not endorse this formalization); Lean code and this site Apache-2.0. Publisher formatting
files from the arXiv archive are not republished.</p>"""
        return self.shell(f"About · {TITLE}", body, "about", toc=False)

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
                if owner and ("E-" + owner["id"]) in where:
                    anchor = "E-" + owner["id"]
                    pid = where[anchor]
            if not pid:
                return esc(text)
            return f'<a class="ref" href="{pid}.html#{attr(anchor)}">{esc(text)}</a>'

        out = {}
        for pid, text in pages.items():
            out[pid] = re.sub(r"@@REF\|(\w)\|(\w+)\|([^@]*)@@", lambda m: fmt(m.group(1), m.group(2), m.group(3)), text)
        self.missing_refs = missing
        return out

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

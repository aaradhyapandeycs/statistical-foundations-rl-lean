"""Status dashboard and dependency-graph pages.

Both pages are computed at build time from the node graph that
`scripts/gen_nodes.py` derives from the ledgers at the reader's Lean revision
(the same function that writes docs/graph/nodes.json), so the site never
carries hand-written counts. The graph is drawn as an inline SVG by a small
deterministic layout (one column per chapter, book order within a column), so
no Graphviz is needed; a DOT file is published beside it for anyone who wants
a Graphviz layout, and a table lists every node and edge as the text fallback.
"""

from __future__ import annotations

import html
import json
import re
import sys
from pathlib import Path

from .lean import marker_toggles
from .tex import html_id, label_id

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
import gen_nodes  # noqa: E402

STATEMENT_WORDS = {
    "printed": "Printed statement",
    "corrected": "Corrected form",
    "restricted": "Restricted form",
    "refuted": "Printed form refuted",
    "partial": "Partial",
    # closing statuses: never proofs (gen_nodes.CLOSING_STATUSES)
    "implied": "Implied by a proved entry, not separately proved",
    "explanatory": "Explanatory, no mathematical claim",
    "cited-out-of-scope": "Cited from the literature; not formalized here (project scope decision); not proved",
    "open": "Open",
    "prose-claim": "Prose claim, no statement entry",
}
PROOF_WORDS = {"proved": "Proved in Lean", "refuted": "Refuted in Lean", "open": "Not proved"}
# Numbers that were assigned to a candidate later withdrawn (the numbers are not reused).
WITHDRAWN_ISSUES = {
    "C11": "withdrawn. An earlier candidate about the learning-rate hypothesis of Lemma 4.8 turned out not to be a "
           "source discrepancy and was removed; the number is not reused.",
}
KIND_SHORT = {"theorem": "Thm", "lemma": "Lem", "claim": "Claim", "remark": "Rem",
              "display": "Eq", "subequations": "Eq"}


def esc(t) -> str:
    return html.escape(str(t), quote=False)


def attr(t) -> str:
    return html.escape(str(t), quote=True)


class GitReader:
    """gen_nodes reader over `git show <rev>:path` (the reader's pinned revision)."""

    def __init__(self, git):
        self.git = git

    def show(self, path: str) -> str:
        return self.git.show(path)

    def ls(self, prefix: str) -> list:
        return self.git.ls(prefix)


# status-table marker columns: (summary key, heading); the order of the columns.
MARKER_COLS = ("refuted", "boundary", "reading", "domain", "illposed", "fails_paper")
MARKER_HEADS = (("refuted", "✕ refuted"), ("boundary", "∂ boundary"), ("reading-dependent", "◇ reading"),
                ("domain", "⊘ domain"), ("ill-posed", "∅ ill-posed"), ("fails-paper", "⚠ paper"))


def status_phrase(n: dict) -> str:
    """The node's reader label in words (one of four, or none), its markers and the incomplete sub-reason."""
    lab = n.get("site_label")
    parts = [gen_nodes.SITE_LABELS[lab][0]] if lab else []
    parts += [gen_nodes.MARKERS[m] for m in n.get("site_markers", [])]
    if n.get("site_sub_reason") and lab in ("incomplete", None):
        parts.append(n["site_sub_reason"])
    return "; ".join(parts)


def fill_class(n: dict) -> str:
    if n["proof_status"] == "refuted":
        return "gn-pf-refuted"
    if n["proof_status"] != "proved":
        return "gn-pf-open"
    if n["printed_with_cited_printed"]:
        return "gn-pf-fully"
    return "gn-pf-proved" if n["statement_status"] == "printed" else "gn-pf-variant"


def short_name(n: dict) -> str:
    """Short node text for the graph; never an internal id."""
    k = KIND_SHORT.get(n["kind"], n["kind"][:5].capitalize())
    num = n.get("number")
    if k == "Eq":
        if num:
            return f"Eq ({num})"
        t = (n.get("tex") or [{}])[0]
        return f'Eq, line {t["line_start"]}' if t else "Eq (unnumbered)"
    return f"{k} {num}" if num else k


def long_name(n: dict) -> str:
    return n.get("display_name") or gen_nodes.display_name(n)


class GraphPages:
    def __init__(self, site, html_pages: dict):
        self.site = site
        self.data = getattr(site, "node_data", None) or gen_nodes.build(GitReader(site.lean.git))
        self.nodes = {n["id"]: n for n in self.data["nodes"]}
        if not getattr(site, "where", None):
            site.where = {}
            for pid, text in html_pages.items():
                for m in re.finditer(r'id="([^"]+)"', text):
                    site.where.setdefault(html.unescape(m.group(1)), pid)
        self.where = site.where
        self.chapter_titles = {p.chapter: p.title for p in site.pages if p.level == 0}

    def chapter_title(self, ch) -> str:
        """Plain-text, escaped chapter title (the reader's titles are converted HTML)."""
        return esc(html.unescape(re.sub(r"<[^>]+>", "", self.chapter_titles.get(ch, ""))))

    # links -------------------------------------------------------------------------
    def href(self, n: dict) -> str | None:
        return self.site.href(n)

    def tex_link(self, n: dict) -> str:
        if not n["tex"]:
            return ""
        t = n["tex"][0]
        return f'<code>{esc(t["file"])}:{t["line_start"]}–{t["line_end"]}</code>'

    def chip(self, n: dict, issues: bool = False) -> str:
        return self.site.node_chip(n, issues)

    # dashboard -----------------------------------------------------------------------
    def status_page(self) -> str:
        site, s = self.site, self.data["summary"]
        cnt = site.cnt
        order = gen_nodes.SITE_LABEL_ORDER
        rows = []
        for ch, c in s["by_chapter"].items():
            if not c["named_total"] and not sum(c["prose"].values()):
                continue
            p = f"by_chapter.{ch}"
            rows.append(
                f'<tr><td>{esc(ch)}</td><td>{self.chapter_title(ch)}</td>'
                f'<td class="num">{cnt(p + ".named_total")}</td>'
                + "".join(f'<td class="num">{cnt(f"{p}.named_by_label.{k}")}</td>' for k in order)
                + "".join(f'<td class="num">{cnt(f"{p}.named_{k}_marker")}</td>' for k in MARKER_COLS)
                + "".join(f'<td class="num">{cnt(f"{p}.prose_by_label.{k}")}</td>' for k in order)
                + "".join(f'<td class="num">{cnt(f"{p}.prose_{k}_marker")}</td>' for k in MARKER_COLS) + '</tr>')
        short = {"stated": "as stated", "corrected": "corrected", "restricted": "restricted", "incomplete": "incomplete"}
        heads = "".join(f'<th><span class="status {gen_nodes.SITE_LABELS[k][1]}" '
                        f'title="{attr(gen_nodes.SITE_LABELS[k][0])}">{esc(short.get(k, gen_nodes.SITE_LABELS[k][0]))}</span></th>'
                        for k in order)
        mheads = "".join(f'<th title="{attr(gen_nodes.MARKERS[m])}">{esc(w)}</th>' for m, w in MARKER_HEADS)
        rev = site.lean.git.rev
        c = s["closing_not_proved"]
        n_issues = len(site.lean.issue_slugs)
        body = f"""<h1>Progress</h1>
<div class="incomplete" role="note"><strong>INCOMPLETE.</strong> The formalization of the monograph is not
complete, and no chapter is certified. These are counts of source items by label, read from the node graph generated
from the project's ledgers at commit <code>{rev[:10]}</code>; reviews are by AI agents (no human referee, no author
approval). They are not a percentage of the book.</div>
<p class="lede">{site.count_sentence()}</p>
{site.stacked_bar()}
<h2>By chapter</h2>
<p class="scroll-hint">The table is wide: scroll it sideways →</p>
<div class="table-wrap"><table class="results dash-table"><thead>
<tr><th rowspan="2">Ch.</th><th rowspan="2">Title</th><th colspan="11">Numbered theorems, lemmas and claims</th>
<th colspan="10">Remarks and displayed claims</th></tr>
<tr><th>Total</th>{heads}{mheads}{heads}{mheads}</tr></thead>
<tbody>{''.join(rows)}</tbody></table></div>
<p class="lede">✕ refuted in Lean counts items whose printed statement appears false in a non-degenerate case under its
natural reading. The other marker columns are qualified failures, none counted as refuted: ∂ boundary case (fails only at a
degenerate boundary point, domain repaired); ◇ reading (refuted only under a stated reading of an ambiguous printed form);
⊘ domain (fails only outside an assumed range or standalone); ∅ ill-posed (the printed formula is undefined at the point,
so Lean's value is a convention); ⚠ fails on paper counts items with no Lean refutation whose printed statement fails by a
paper argument of this project (not checked in Lean). All of them also carry one of the four labels (a corrected form may
be proved). A chapter whose numbered results all have a label
other than incomplete is still not certified: its prose claims, algorithms and arguments are not all formalized.</p>
<h2>What is not in these counts</h2>
<ul>
<li>{site.cntw("prose_by_label.no_claim", "remark or display", "remarks or displays")} the coverage ledger reviews as making no mathematical claim
(no label).</li>
<li>Among the incomplete remarks and displays: {cnt("closing_not_proved.implied.nodes")} implied by a proved entry (not
separately proved) and {cnt("closing_not_proved.cited-out-of-scope.nodes")} cited from the literature and out of scope
by a project decision. Coverage rows with no inventory item: {cnt("closing_not_proved.implied.rows_without_node")}
implied, {cnt("closing_not_proved.explanatory.rows_without_node")} explanatory,
{cnt("closing_not_proved.cited-out-of-scope.rows_without_node")} cited and out of scope.</li>
<li>{cnt("context_items.algorithm")} algorithms, {cnt("context_items.definition")} definitions and
{cnt("context_items.assumption")} assumptions (no label), {cnt("source_gap_candidates")} source-gap candidates in the
inventory, and unlabelled prose claims not listed in the coverage ledger. The inventory's source-gap candidates are
unreviewed keyword hits (phrases such as “omitted” or a proof deferred to the literature), flagged for manual review and
not claims of error; they are a different list from the {n_issues} reviewed source-issue candidates on the
<a href="errata.html#all">Source issues</a> page, which come from <code>docs/SOURCE-ISSUES.md</code>.</li>
</ul>
{self.warnings_html()}
<h2>How these numbers are made</h2>
<p><code>scripts/gen_nodes.py</code> reads the source inventory, the named-result ledger, the coverage ledger, the
source-issues list and the statement index at commit <code>{rev[:10]}</code>, gives every item one of the four labels
and writes the counts into the <code>summary</code> of <a href="graph/nodes.json">graph/nodes.json</a>. Every number
on this site is read from that summary, and the site build fails if any shown number differs from it. A numbered result
is proved only if the named-result ledger has a record for it; the generator cross-checks that against a direct count
of distinct ledger keys and the inventory's count of numbered results (a bookkeeping check, not an independent review
of the ledger). Open items are in <a href="{attr(site.lean.git.blob('docs/NEXT.md'))}">docs/NEXT.md</a>. See also the
<a href="graph.html">dependency graph</a> and the <a href="results.html">results index</a>.</p>"""
        return site.shell(f"Progress · {self.site_title()}", body, "status", toc=False)

    def warnings_html(self) -> str:
        w = self.data["warnings"]
        if not w:
            return ""
        def plain(x: str) -> str:
            m = re.match(r"(.+?): proved by the ledgers, but a COVERAGE headline says (\w+); the headline wins$", x)
            if m:
                n = self.nodes.get(m.group(1))
                who = (f"{long_name(n)}{' (' + n['labels'][0] + ')' if n['labels'] else ''}" if n
                       else m.group(1).replace("label:", "item ", 1))
                return (f"{who}: the ledgers record a "
                        f"proof, but the coverage-ledger headline says {m.group(2)}; counted as {m.group(2)}.")
            return x
        items = "".join(f"<li>{esc(plain(x))}</li>" for x in w)
        return (f'<details class="gwarn-box"><summary>Known bookkeeping notes</summary>'
                f'<p class="lede">Notes for the maintainers from the program that computes these counts. Where the '
                f'two ledgers disagree, the more cautious reading is used. The full list is in '
                f'<a href="{attr(self.site.lean.git.blob("docs/NEXT.md"))}">docs/NEXT.md</a>.</p>'
                f'<ul class="gwarn">{items}</ul></details>')

    def site_title(self) -> str:
        from .render import TITLE
        return TITLE

    # graph ---------------------------------------------------------------------------
    def svg(self) -> str:
        cols = {}
        for n in self.data["nodes"]:
            cols.setdefault(n["chapter"], []).append(n)
        chapters = sorted(cols, key=lambda c: int(c or 0))
        W, H, GX, GY, TOP, LEFT = 132, 22, 96, 8, 46, 12
        pos = {}
        for ci, ch in enumerate(chapters):
            for ri, n in enumerate(cols[ch]):
                pos[n["id"]] = (LEFT + ci * (W + GX), TOP + ri * (H + GY))
        # a second layout with numbered results only (default view); edges through hidden nodes collapse
        npos = {}
        # chapters with no numbered result get no column in this view (no blank panel on narrow screens)
        ncols = [ch for ch in chapters if any(x["class"] == "named" for x in cols[ch])]
        nx = {ch: LEFT + i * (W + GX) for i, ch in enumerate(ncols)}
        for ch in ncols:
            for ri, n in enumerate([x for x in cols[ch] if x["class"] == "named"]):
                npos[n["id"]] = (nx[ch], TOP + ri * (H + GY))
        width = LEFT * 2 + len(chapters) * (W + GX) - GX
        nwidth = LEFT * 2 + len(ncols) * (W + GX) - GX
        height = TOP + max(len(v) for v in cols.values()) * (H + GY) + 10
        nheight = TOP + max(sum(1 for x in v if x["class"] == "named") for v in cols.values()) * (H + GY) + 10
        out = [f'<svg class="depgraph" xmlns="http://www.w3.org/2000/svg" width="{width}" height="{nheight}" '
               f'viewBox="0 0 {width} {nheight}" data-w="{width}" data-w-named="{nwidth}" data-h-all="{height}" data-h-named="{nheight}" '
               f'role="group" aria-labelledby="gtitle">'
               '<title id="gtitle">Dependency graph of the book\'s results, one column per chapter</title>'
               '<defs><marker id="arrow" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" '
               'orient="auto-start-reverse"><path d="M0,0 L8,4 L0,8 z" class="gn-arrow"/></marker>'
               '<clipPath id="nclip"><rect x="0" y="0" width="124" height="22"/></clipPath></defs>']
        for ci, ch in enumerate(chapters):
            x = LEFT + ci * (W + GX)
            out.append(f'<text x="{x}" y="22" class="gn-col" data-ch="{attr(ch)}" data-x="{x}" '
                       f'data-nx="{nx.get(ch, "")}">Chapter {esc(ch)}</text>')

        def path(p1, p2):
            (x1, y1), (x2, y2) = p1, p2
            y1c, y2c = y1 + H / 2, y2 + H / 2
            if x1 == x2:
                bend = W + 18 + min(60, abs(y2 - y1) / 8)
                return f"M{x1 + W},{y1c} C{x1 + bend},{y1c} {x2 + bend},{y2c} {x2 + W},{y2c}"
            if x1 < x2:
                return f"M{x1 + W},{y1c} C{x1 + W + GX / 2},{y1c} {x2 - GX / 2},{y2c} {x2},{y2c}"
            return f"M{x1},{y1c} C{x1 - GX / 2},{y1c} {x2 + W + GX / 2},{y2c} {x2 + W},{y2c}"

        uses = {n["id"]: [u["id"] for u in n["uses"] if gen_nodes.is_dependency(u) and u["id"] in pos]
                for n in self.data["nodes"]}

        def named_uses(nid):
            """Named results reached from nid's uses, passing through prose nodes."""
            seen, stack, found = set(), list(uses[nid]), []
            while stack:
                x = stack.pop()
                if x in seen:
                    continue
                seen.add(x)
                if self.nodes[x]["class"] == "named":
                    found.append(x)
                else:
                    stack.extend(uses.get(x, []))
            return sorted(set(found) - {nid})

        for n in self.data["nodes"]:
            for uid in uses[n["id"]]:
                out.append(f'<path d="{path(pos[uid], pos[n["id"]])}" class="gn-edge e-all" data-from="{attr(html_id(uid))}" '
                           f'data-to="{attr(html_id(n["id"]))}" marker-end="url(#arrow)"/>')
        for n in self.data["nodes"]:
            if n["class"] != "named":
                continue
            for uid in named_uses(n["id"]):
                out.append(f'<path d="{path(npos[uid], npos[n["id"]])}" class="gn-edge e-named" '
                           f'data-from="{attr(html_id(uid))}" data-to="{attr(html_id(n["id"]))}" marker-end="url(#arrow)"/>')
        for n in self.data["nodes"]:
            x, y = pos[n["id"]]
            nx, ny = npos.get(n["id"], (x, y))
            title = (f'{long_name(n)}{" " + n["labels"][0] if n["labels"] else ""}: {status_phrase(n)}'
                     f'{"; " + ", ".join(n["issues"]) if n["issues"] else ""}')
            lab = n.get("site_label") or "none"
            marks = n.get("site_markers", [])
            text = next((g + " " for m, g in (("refuted", "✕"), ("boundary", "∂"), ("reading-dependent", "◇"),
                                              ("domain", "⊘"), ("ill-posed", "∅"), ("fails-paper", "⚠"))
                         if m in marks), "") + short_name(n)
            cls = f'gn gl-{lab}{" mk-new" if "new-proof" in marks else ""}{" named" if n["class"] == "named" else " prose"}'
            node = (f'<g class="{cls}" data-id="{attr(html_id(n["id"]))}" data-ch="{attr(n["chapter"])}" '
                    f'data-named="{1 if n["class"] == "named" else 0}" '
                    f'data-uses="{attr(" ".join(html_id(u) for u in uses[n["id"]]))}" '
                    f'data-nuses="{attr(" ".join(html_id(u) for u in named_uses(n["id"])) if n["class"] == "named" else "")}" '
                    f'data-xy="{x},{y}" data-nxy="{nx},{ny}" transform="translate({nx},{ny})">'
                    f'<title>{esc(title)}</title>'
                    f'<rect x="0" y="0" width="{W}" height="{H}" rx="4"/>'
                    f'<text x="{W / 2}" y="15" clip-path="url(#nclip)" textLength="{min(W - 8, 7 * len(text))}" '
                    f'lengthAdjust="spacingAndGlyphs">{esc(text)}</text></g>')
            out.append(f'<a href="#n-{attr(html_id(n["id"]))}" aria-label="{attr(long_name(n))}">{node}</a>')
        out.append("</svg>")
        return "".join(out)

    def dot(self) -> str:
        lines = ["// Generated by site/build.py from the node graph; render with: dot -Tsvg graph.dot",
                 "digraph results {", "  rankdir=LR; node [shape=box, fontsize=10];"]
        fill = {"stated": "palegreen", "corrected": "khaki", "restricted": "thistle", "incomplete": "white",
                "none": "gray95"}
        for n in self.data["nodes"]:
            lab = n.get("site_label") or "none"
            style = "filled,dashed" if "new-proof" in n.get("site_markers", []) else "filled"
            mk = n.get("site_markers", [])
            color = ("red" if "refuted" in mk else
                     "orange" if {"boundary", "reading-dependent", "domain", "ill-posed", "fails-paper"} & set(mk)
                     else "black")
            lines.append(f'  "{n["id"]}" [label="{long_name(n)}", style="{style}", color={color}, '
                         f'fillcolor={fill[lab]}];')
        for n in self.data["nodes"]:
            for u in n["uses"]:
                if gen_nodes.is_dependency(u):
                    lines.append(f'  "{u["id"]}" -> "{n["id"]}";')
        lines.append("}")
        return "\n".join(lines) + "\n"

    def graph_page(self) -> str:
        legend = "".join(
            f'<li><svg width="46" height="20" aria-hidden="true"><g class="gn gl-{k}">'
            f'<rect x="2" y="2" width="42" height="16" rx="3"/></g></svg> {esc(gen_nodes.SITE_LABELS[k][0])}</li>'
            for k in gen_nodes.SITE_LABEL_ORDER)
        legend += ('<li><svg width="46" height="20" aria-hidden="true"><g class="gn gl-none">'
                   '<rect x="2" y="2" width="42" height="16" rx="3"/></g></svg> no mathematical claim (no label)</li>'
                   '<li><span class="gmark">✕</span> printed statement refuted in Lean (non-degenerate case, '
                   'natural reading)</li>'
                   '<li><span class="gmark soft">∂</span> printed statement fails only at a boundary case '
                   '(domain repaired)</li>'
                   '<li><span class="gmark soft">◇</span> refuted only under a stated reading</li>'
                   '<li><span class="gmark soft">⊘</span> fails only outside an assumed domain</li>'
                   '<li><span class="gmark soft">∅</span> printed formula undefined at the point (Lean value is a '
                   'convention)</li>'
                   '<li><span class="gmark soft">⚠</span> printed statement appears to fail (paper argument, not '
                   'checked in Lean)</li>'
                   '<li><svg width="46" height="20" aria-hidden="true"><g class="gn gl-stated mk-new">'
                   '<rect x="2" y="2" width="42" height="16" rx="3"/></g></svg> dashed border: new proof</li>')
        trs, last = [], None
        for n in self.data["nodes"]:
            if n["chapter"] != last:
                last = n["chapter"]
                trs.append(f'<tr class="ch-row" data-ch="{attr(last)}"><th colspan="5">Chapter {esc(last)} '
                           f'{self.chapter_title(last)}</th></tr>')
            link = self.href(n)
            name = esc(long_name(n))
            name = f'<a href="{attr(link)}">{name}</a>' if link else name
            lab = f'<div class="label"><code>{esc(n["labels"][0])}</code></div>' if n["labels"] else ""
            uses = ", ".join(
                f'<a href="#n-{attr(html_id(u["id"]))}">{esc(long_name(self.nodes[u["id"]]))}</a>'
                for u in n["uses"] if gen_nodes.is_dependency(u))
            ctx = [u for u in n["uses"] if not gen_nodes.is_dependency(u) and u.get("verdict") != "wrong-target"]
            if ctx:
                uses += (", " if uses else "") + f'{len(ctx)} context reference{"s" if len(ctx) > 1 else ""} (definition, algorithm or comparison)'
            lean = " ".join(f'<code title="{attr(e["name"])}">{esc(e["name"].rsplit(".", 1)[-1])}</code>'
                            for e in n["statement_entries"])
            search = " ".join([long_name(n), n["labels"][0] if n["labels"] else "", lean,
                               " ".join(n["issues"])]).lower()
            trs.append(f'<tr id="n-{attr(html_id(n["id"]))}" data-label="{attr(n.get("site_label") or "none")}" '
                       f'data-markers="{attr(" ".join(n.get("site_markers", [])))}" data-ch="{attr(n["chapter"])}" '
                       f'data-named="{1 if n["class"] == "named" else 0}" '
                       f'data-search="{attr(re.sub("<[^>]+>", "", search))}">'
                       f'<td data-th="Item">{name}{lab}<div class="label">{self.tex_link(n)}</div></td>'
                       f'<td data-th="Status">{self.chip(n, issues=True)}</td>'
                       f'<td data-th="Lean" class="lean-names">{lean or "—"}</td>'
                       f'<td data-th="Cites">{uses or "—"}</td></tr>')
        chapters = "".join(f'<option value="{attr(c)}">Chapter {esc(c)}</option>'
                           for c in sorted({n["chapter"] for n in self.data["nodes"]}, key=lambda c: int(c or 0)))
        s = self.data["summary"]
        cnt = self.site.cnt
        body = f"""<h1>Dependency graph</h1>
<div class="incomplete" role="note"><strong>AI-reviewed edges.</strong> Arrows are read from the TeX
cross-references (<code>\\ref</code>, <code>\\eqref</code>, …) inside each result and its proof, plus
{cnt("uses_edges_added_by_review")} dependencies the review found without a reference. Of these {cnt("uses_edges")}
edges, {cnt("uses_edges_reviewed")} were classified by an AI critic; an independent AI verifier re-checked every comparison, wrong-target and added edge and a random sample of 40 others (not
author-reviewed); arrows are proof dependencies only, while definition and comparison references are listed as context
and wrong-target references are dropped. A real dependency may still be cited without a reference. The graph does not
certify a chapter or the book.</div>
<p class="lede">One node per numbered theorem, lemma and claim ({cnt("named_results_in_inventory")}), plus remarks and
displayed claims ({cnt("prose_nodes")}). The fill is the item's label; arrows point from a cited result to the result
that cites it. Click a node to highlight what it cites (transitively) and what cites it; click it again to go to its
row. <a href="status.html">Counts by chapter</a> · <a href="graph/nodes.json">nodes.json</a> ·
<a href="graph/graph.dot">graph.dot</a> (Graphviz).</p>
<ul class="glegend">{legend}</ul>
<div class="graph-controls" role="group" aria-label="Graph controls">
<label class="toggle"><input type="checkbox" id="g-named" checked> numbered results only</label>
<select id="g-ch" aria-label="Chapter"><option value="">All chapters</option>{chapters}</select>
<button type="button" class="chip" id="g-zoom-out" aria-label="Zoom out">−</button>
<button type="button" class="chip" id="g-zoom-in" aria-label="Zoom in">+</button>
<button type="button" class="chip" id="g-clear">Clear highlight</button>
<span id="g-info" class="g-info" aria-live="polite"></span></div>
<p class="scroll-hint">Scroll the graph sideways to see every chapter →</p>
<div class="graph-wrap">{self.svg()}</div>
<h2>All nodes</h2>
<div class="filters"><input type="search" id="q" placeholder="Search number, label, Lean name or C-id" aria-label="Search nodes">
<div class="chips"><button type="button" class="chip on" data-filter="" aria-pressed="true">All</button>{"".join(
    f'<button type="button" class="chip" data-filter="{k}" aria-pressed="false"><span class="status {gen_nodes.SITE_LABELS[k][1]}">'
    f'{esc(gen_nodes.SITE_LABELS[k][0])}</span></button>' for k in gen_nodes.SITE_LABEL_ORDER)}
<label class="toggle"><input type="checkbox" id="f-refuted"> <span class="marker mk-refuted">{esc(gen_nodes.MARKERS["refuted"])}</span></label>
{marker_toggles()}
<label class="toggle"><input type="checkbox" id="f-named"> numbered results only</label></div>
<p class="filter-count" aria-live="polite"></p></div>
<div class="table-wrap"><table class="results stack graph-table"><thead><tr><th>Item</th><th>Status</th>
<th>Statement entries</th><th>Cites (proof dependencies; AI-reviewed)</th></tr></thead>
<tbody>{''.join(trs)}</tbody></table></div>
<p class="lede">Definitions, assumptions and algorithms are context, not nodes; references to them are counted but
never block.</p>"""
        return self.site.shell(f"Dependency graph · {self.site_title()}", body, "graph", toc=False)

    def errata_page(self) -> str:
        """Source issues grouped by what they mean for a result, from SOURCE-ISSUES.md and the node graph."""
        lean = self.site.lean
        issues_url = lean.git.blob("docs/SOURCE-ISSUES.md")
        by_issue: dict = {}
        for n in self.data["nodes"]:
            for c in n["issues"]:
                by_issue.setdefault(c, []).append(n)

        def node_link(n):
            link = self.href(n)
            name = esc(long_name(n))
            return f'<a href="{attr(link)}">{name}</a>' if link else name

        def issues(n):
            return lean.issue_links([c[1:] for c in n["issues"] if c[1:] in lean.issue_slugs])

        def table(ns, extra_head, extra):
            rows = "".join(f'<tr><td data-th="Item">{node_link(n)}<div class="label"><code>'
                           f'{esc(n["labels"][0] if n["labels"] else "")}</code></div></td>'
                           f'<td data-th="Status">{self.chip(n)}</td><td data-th="{extra_head}">{extra(n)}</td>'
                           f'<td data-th="Source issue">{issues(n) or "—"}</td></tr>' for n in ns)
            if not rows:
                return "<p>None.</p>"
            return (f'<div class="table-wrap"><table class="results stack"><thead><tr><th>Item</th><th>Status</th>'
                    f'<th>{extra_head}</th><th>Source issue</th></tr></thead><tbody>{rows}</tbody></table></div>')

        ours = "proposed by this project; not confirmed by the authors"
        nodes = self.data["nodes"]
        refuted = [n for n in nodes if "refuted" in n.get("site_markers", [])]
        paper = [n for n in nodes if "fails-paper" in n.get("site_markers", [])]
        boundary = [n for n in nodes if "boundary" in n.get("site_markers", [])]
        reading = [n for n in nodes if "reading-dependent" in n.get("site_markers", [])]
        domain = [n for n in nodes if "domain" in n.get("site_markers", [])]
        illposed = [n for n in nodes if "ill-posed" in n.get("site_markers", [])]
        corrected = [n for n in nodes if n.get("site_label") == "corrected" or "also-corrected" in n.get("site_markers", [])]
        restricted = [n for n in nodes if n.get("site_label") == "restricted" and n not in corrected]
        repaired = [n for n in nodes if "source-proof-repaired" in n.get("proof_origins", [])]
        crows = []
        for cid, info in sorted(lean.issue_slugs.items(), key=lambda kv: int(kv[0])):
            ns = by_issue.get(f"C{cid}", [])
            items = ", ".join(f'{node_link(n)} ({esc(status_phrase(n))})' for n in ns)
            crows.append(f'<tr><td data-th="Id"><a href="{attr(issues_url)}#{attr(info["slug"])}">C{esc(cid)}</a></td>'
                         f'<td data-th="Candidate">{esc(re.sub(r"^(Candidate )?C[0-9]+: *", "", info["title"]))}</td>'
                         f'<td data-th="Items">{items or "No tracked item cites it (see the entry)"}</td></tr>')
        ids = sorted(int(c) for c in lean.issue_slugs)
        gaps = [f"C{i}" for i in range(ids[0], ids[-1] + 1) if str(i) not in lean.issue_slugs] if ids else []
        gap_note = "".join(f" {g}: {WITHDRAWN_ISSUES.get(g, 'not used.')}" for g in gaps)
        n_gap = self.data["summary"].get("source_gap_candidates", 0)
        gap_note += (f" These {len(ids)} reviewed candidates are not the {n_gap} “source-gap candidates” counted on the "
                     f'<a href="status.html">Progress</a> page: those are unreviewed keyword hits in the source inventory '
                     f"(for example “omitted” or a proof deferred to the literature), flagged for manual review, not "
                     f"claims of error.")
        rev = lean.git.rev
        def refs(n):
            pr = n.get("printed_refuted") or {}
            names = " ".join(f'<code title="{attr(x)}">{esc(x.rsplit(".", 1)[-1])}</code>'
                             for x in (pr.get("lean") or n["refutations_cited"])) or "see the coverage ledger"
            return names + (f'<br><span class="reading tex2jax_process">Reading: {lean.md(pr["reading"])}</span>' if pr.get("reading") else "")

        def paper_case(n):
            pr = n.get("printed_refuted") or {}
            r = lean.md(pr.get("reading", ""))
            return f'<span class="tex2jax_process">{r}</span>' if r else "see the source issue"
        body = f"""<h1>Source issues</h1>
<div class="incomplete" role="note"><strong>Candidates, not confirmed errata.</strong> Every item below was found by
reviews performed by AI agents against the pinned TeX of arXiv:2610.41903v1. Every refutation, correction and
restriction here is {ours}. A Lean refutation is a machine-checked proof that the printed statement, <em>under the
reading the project formalized</em>, is false; the reading itself is part of what a reader should check. Only the
items in section (a) are false in a non-degenerate case under their natural reading; the sections after it are
qualified (degenerate boundary, ambiguous reading, outside an assumed domain, undefined formula).</div>
<p class="lede">Generated at build time from <code>docs/SOURCE-ISSUES.md</code>, the coverage ledger and the
named-result ledger at commit <code>{rev[:10]}</code>. The curated record with effects on each result is
<a href="{attr(lean.git.blob("docs/ERRATA-AND-DEVIATIONS.md"))}">docs/ERRATA-AND-DEVIATIONS.md</a>.</p>
<nav class="page-toc"><a href="#refuted">Refuted in Lean</a> · <a href="#boundary">Boundary cases</a> · <a href="#reading">Reading-dependent</a> · <a href="#domain">Outside assumed domain</a> · <a href="#illposed">Ill-posed</a> · <a href="#paper">Failing on paper</a> · <a href="#corrections">Corrections</a> ·
<a href="#restrictions">Restrictions</a> · <a href="#repaired">Proof gaps repaired</a> · <a href="#all">All candidates</a></nav>
<h2 id="refuted">(a) Printed statements refuted in Lean (non-degenerate case, natural reading)</h2>
<p class="lede">Items for which the named-result ledger (field <code>printed_refuted</code>, kind
<code>counterexample</code>) lists Lean theorems that refute the printed statement in a non-degenerate case under its
natural reading. Most items are proved in a corrected or restricted form as well; the label says so. Items classed
below as boundary, reading-dependent, outside an assumed domain or ill-posed are not counted here.</p>
{table(refuted, "Lean refutation", refs)}
<h2 id="boundary">(a″) Printed statements that fail only at a boundary case (domain repaired)</h2>
<p class="lede">Items for which Lean shows the printed statement fails, but only at a degenerate boundary or domain case
(for example T = 1, where the printed schedule divides by log T = 0, or a single action, where every policy is
optimal); adding the missing domain condition repairs it. They are not counted with (a).</p>
{table(boundary, "Lean theorem (boundary case)", refs)}
<h2 id="reading">(a‴) Printed statements refuted only under a stated reading</h2>
<p class="lede">The printed form is ambiguous; Lean refutes it under the reading stated in each row, and under the other
natural reading no counterexample is claimed. They are not counted with (a).</p>
{table(reading, "Lean theorem (stated reading)", refs)}
<h2 id="domain">(a⁗) Printed statements that fail only outside an assumed domain</h2>
<p class="lede">The failure lies outside a parameter range or premise assumed elsewhere in the book, or the statement is
read standalone. They are not counted with (a).</p>
{table(domain, "Failing case", refs)}
<h2 id="illposed">(a⁵) Printed formula undefined at the point</h2>
<p class="lede">The printed formula is undefined where Lean's statement fails, so Lean's value is a convention (for
example x/0 = 0) and this is not a refutation of a well-defined case. They are not counted with (a).</p>
{table(illposed, "Lean theorem (convention)", refs)}
<h2 id="paper">(a′) Printed statements that appear to fail (paper argument)</h2>
<p class="lede">Items of kind <code>counterexample</code> with no Lean refutation for which a paper argument by this project, not checked in Lean, shows
that the printed statement fails. These are weaker evidence than (a).</p>
{table(paper, "Failing case", paper_case)}
<h2 id="corrections">(b) Corrections we propose</h2>
<p class="lede">Items proved only in a corrected form. Each correction is {ours}; the card on the book page says what
differs from the print.</p>
{table(corrected, "Lean entries", lambda n: " ".join(f'<code>{esc(e["name"].rsplit(".", 1)[-1])}</code>' for e in n["statement_entries"] if e.get("counted", True)))}
<h2 id="restrictions">(c) Restrictions and scope disclosures</h2>
<p class="lede">Items proved for a special case of the printed statement. The restriction is {ours}. Further
limits of the formalization (conventions, not asserted errors) are in
<a href="{attr(issues_url)}#statement-index-scope-disclosures">Statement-index scope disclosures</a>.</p>
{table(restricted, "Lean entries", lambda n: " ".join(f'<code>{esc(e["name"].rsplit(".", 1)[-1])}</code>' for e in n["statement_entries"] if e.get("counted", True)))}
<h2 id="repaired">(d) Proof gaps repaired</h2>
<p class="lede">Items whose Lean proof follows the book's argument with gaps repaired (ledger field
<code>proof_origin</code>). The repairs are {ours}.</p>
{table(repaired, "Origin", lambda n: "book's proof, gaps repaired") if repaired else "<p>None recorded in the ledger yet.</p>"}
<h2 id="all">All source-issue candidates</h2>
<p class="lede">Each links to its entry in SOURCE-ISSUES.md, which states the evidence and any proposed correction.
An issue may concern the book's proof (a gap or a slip) rather than its statement; a label on the statement says
nothing about whether the book's argument is complete.{gap_note}</p>
<div class="table-wrap"><table class="results stack"><thead><tr><th>Id</th><th>Candidate</th><th>Items</th></tr></thead>
<tbody>{"".join(crows)}</tbody></table></div>"""
        return self.site.shell(f"Source issues · {self.site_title()}", body, "errata", toc=False)

    def nodes_json(self) -> str:
        return gen_nodes.dumps(self.data)

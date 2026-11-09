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

from .tex import label_id

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
    "cited-out-of-scope": "Cited result, out of scope by user decision; not proved",
    "open": "Open",
    "prose-claim": "Prose claim, no statement entry",
}
PROOF_WORDS = {"proved": "Proved in Lean", "refuted": "Refuted in Lean", "open": "Not proved"}
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


def status_phrase(n: dict) -> str:
    if n["proof_status"] == "proved":
        return {"printed": "proved as printed", "corrected": "corrected form proved",
                "restricted": "restricted form proved"}.get(n["statement_status"], "proved")
    if n["statement_status"] == "implied":
        return f'implied by a {n.get("implied_variant") or "proved"} entry, not separately proved'
    return STATEMENT_WORDS[n["statement_status"]].lower()


def fill_class(n: dict) -> str:
    if n["proof_status"] == "refuted":
        return "gn-pf-refuted"
    if n["proof_status"] != "proved":
        return "gn-pf-open"
    if n["printed_with_cited_printed"]:
        return "gn-pf-fully"
    return "gn-pf-proved" if n["statement_status"] == "printed" else "gn-pf-variant"


def short_name(n: dict) -> str:
    k = KIND_SHORT.get(n["kind"], n["kind"][:5].capitalize())
    num = n.get("number") or (n["labels"][0] if n["labels"] else n["id"])
    if k == "Eq":
        return f"Eq ({num})"
    return f"{k} {num}"


def long_name(n: dict) -> str:
    kind = "Display" if n["kind"] in ("display", "subequations") else n["kind"].capitalize()
    num = n.get("number") or ""
    if kind == "Display":
        return f"Display ({num})" if num else "Display"
    return f"{kind} {num}".strip()


class GraphPages:
    def __init__(self, site, html_pages: dict):
        self.site = site
        self.data = getattr(site, "node_data", None) or gen_nodes.build(GitReader(site.lean.git))
        self.nodes = {n["id"]: n for n in self.data["nodes"]}
        self.where = {}
        for pid, text in html_pages.items():
            for m in re.finditer(r'id="([^"]+)"', text):
                self.where.setdefault(html.unescape(m.group(1)), pid)
        self.chapter_titles = {p.chapter: p.title for p in site.pages if p.level == 0}

    def chapter_title(self, ch) -> str:
        """Plain-text, escaped chapter title (the reader's titles are converted HTML)."""
        return esc(html.unescape(re.sub(r"<[^>]+>", "", self.chapter_titles.get(ch, ""))))

    # links -------------------------------------------------------------------------
    def href(self, n: dict) -> str | None:
        cands = [label_id(l) for l in n["labels"]] + ["E-" + n["id"]]
        for a in cands:
            if a in self.where:
                return f"{self.where[a]}.html#{a}"
        return None

    def tex_link(self, n: dict) -> str:
        if not n["tex"]:
            return ""
        t = n["tex"][0]
        return f'<code>{esc(t["file"])}:{t["line_start"]}–{t["line_end"]}</code>'

    # dashboard -----------------------------------------------------------------------
    def status_page(self) -> str:
        s = self.data["summary"]
        named = s["named_by_statement_status"]
        rows = []
        for ch, c in s["by_chapter"].items():
            if not c["named_total"] and not sum(c["prose"].values()):
                continue
            nm = c["named"]
            prose_proved = sum(c["prose"][k] for k in ("printed", "corrected", "restricted"))
            prose_total = sum(c["prose"].values())
            rows.append(
                f'<tr><td>{esc(ch)}</td><td>{self.chapter_title(ch)}</td>'
                f'<td class="num">{c["named_proved"]} of {c["named_total"]}</td>'
                f'<td class="num">{nm["printed"]}</td><td class="num">{nm["corrected"]}</td>'
                f'<td class="num">{nm["restricted"]}</td><td class="num">{nm["refuted"]}</td>'
                f'<td class="num">{nm["open"] + nm["partial"]}</td>'
                f'<td class="num">{c["named_printed_with_cited_printed"]}</td>'
                f'<td class="num">{prose_proved} of {prose_total}</td></tr>')
        tot_named = s["named_results_in_inventory"]
        recorded = s["named_results_with_ledger_record"]
        prose = s["prose_by_statement_status"]
        ctx = s["context_items"]
        rev = self.site.lean.git.rev
        body = f"""<h1>Formalization status</h1>
<div class="incomplete" role="note"><strong>INCOMPLETE.</strong> The formalization of the monograph is not
complete, and no chapter is certified. The counts below are numbers of source results with a Lean record in
the project's ledgers, whose reviews are independent AI-agent reviews (no human referee, no author approval); they are not a percentage of the book, which also contains prose claims, algorithms and arguments that
these counts do not cover.</div>
<section class="dash">
<div class="tile"><div class="big">{recorded} <span>of {tot_named}</span></div>
<div>numbered theorems, lemmas and claims have a ledger record, reviewed by independent AI agents (in printed, corrected or restricted
form). Counted from <code>docs/named-result-status.json</code> at <code>{rev[:10]}</code>.</div></div>
<div class="tile"><div class="big">{named["printed"]} <span>of {tot_named}</span></div>
<div>proved as printed. {named["corrected"]} more are proved only in corrected form and {named["restricted"]}
only in restricted form; those are <em>not</em> proofs of the printed statement.{esc(self.site.restricted_note(named["restricted"]))}</div></div>
<div class="tile"><div class="big">{named["refuted"] + named["open"] + named["partial"]} <span>of {tot_named}</span></div>
<div>{"has" if named["refuted"] + named["open"] + named["partial"] == 1 else "have"} no proved Lean statement: {named["refuted"]} printed statement refuted in Lean{self.refuted_readings()} with no corrected
version proved, {named["open"]} open, {named["partial"]} partial.</div></div>
<div class="tile"><div class="big">{s["named_printed_with_cited_printed"]} <span>of {tot_named}</span></div>
<div>are proved as printed and every result they cite (transitively) is too. The citations are
<strong>unreviewed</strong> TeX cross-references: this is not a reviewed proof-dependency check, and it does not
say that the cited results are what the proof needs.</div></div>
</section>
<h2>By chapter</h2>
<div class="table-wrap"><table class="results dash-table"><thead><tr><th>Ch.</th><th>Title</th>
<th>Numbered results with ledger record</th><th>Printed</th><th>Corrected</th><th>Restricted</th>
<th>Refuted, nothing proved</th><th>Open or partial</th><th>Printed with all cited results printed*</th>
<th>Remarks and displayed claims proved (any form)</th></tr></thead><tbody>{''.join(rows)}</tbody></table></div>
<p class="lede">* Computed over unreviewed TeX cross-references. A row's counts cover only its numbered
results; a chapter with every numbered result recorded is still not certified, because its prose claims,
algorithms and arguments are not all formalized.</p>
<h2>Outside these counts</h2>
<ul>
<li>{s["prose_nodes"]} remarks and displayed claims tracked as nodes: {prose["printed"]} printed,
{prose["corrected"]} corrected, {prose["restricted"]} restricted, {prose["refuted"]} printed form refuted
with nothing proved, {prose["partial"]} partial,
{prose["prose-claim"]} with nothing recorded beyond, at most, a coverage note.</li>
<li>Not proved and never counted as proved: {self.closing_counts()}.</li>
<li>{ctx["algorithm"]} algorithms, {ctx["definition"]} definitions, {ctx["assumption"]} assumptions.</li>
<li>{s["source_gap_candidates"]} source-gap candidates in the inventory, and unlabelled prose claims not listed
in the coverage ledger.</li>
</ul>
{self.warnings_html()}
<h2>How these numbers are made</h2>
<p><code>scripts/gen_nodes.py</code> reads the source inventory, the named-result ledger, the coverage ledger,
the source-issues list and the statement index at commit <code>{rev[:10]}</code>. A numbered result counts as
proved only if the named-result ledger has a record for it; the generator cross-checks that number against a direct
count of the distinct ledger keys and the inventory's count of numbered results, and refuses to build on a mismatch
(a bookkeeping check, not an independent review of the ledger). A result proved in some form is never shown as
refuted; a node is shown refuted only when nothing is proved and its coverage row cites a Lean refutation of the
printed statement. Corrected and restricted forms are counted separately and never as
the printed result. The same data is published as <a href="graph/nodes.json">graph/nodes.json</a>; open items
are in <a href="{attr(self.site.lean.git.blob('docs/NEXT.md'))}">docs/NEXT.md</a>. See also the
<a href="graph.html">dependency graph</a>.</p>"""
        return self.site.shell(f"Status · {self.site_title()}", body, "status", toc=False)

    def closing_counts(self) -> str:
        c = self.data["summary"]["closing_not_proved"]
        words = {"implied": "implied by a proved entry (the implication is not a separate Lean statement; "
                            "it inherits the entry's corrected or restricted form)",
                 "explanatory": "explanatory, making no mathematical claim",
                 "cited-out-of-scope": "results the book cites from the literature, recorded as out of scope "
                                       "by a dated user decision"}
        return "; ".join(f'{c[k]["nodes"]} nodes and {c[k]["rows_without_node"]} unlabelled ledger rows '
                         f'{esc(words[k])}' for k in gen_nodes.CLOSING_STATUSES)

    def refuted_readings(self) -> str:
        from .lean import REFUTED_READING
        notes = [REFUTED_READING[l] for n in self.data["nodes"] if n["class"] == "named"
                 and n["statement_status"] == "refuted" for l in n["labels"] if l in REFUTED_READING]
        return f' ({esc("; ".join(notes))})' if notes else ""

    def warnings_html(self) -> str:
        w = self.data["warnings"]
        if not w:
            return ""
        items = "".join(f"<li>{esc(x)}</li>" for x in w)
        return (f'<details class="gwarn-box"><summary>Coverage rows not matched to a node ({len(w)})</summary>'
                f'<p class="lede">Generator warnings: these coverage-ledger rows or statement entries could not be '
                f'attached to a source result, so they are not reflected in the counts or the graph. The full list is '
                f'in <a href="{attr(self.site.lean.git.blob("docs/NEXT.md"))}">docs/NEXT.md</a>.</p>'
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
        width = LEFT * 2 + len(chapters) * (W + GX) - GX
        height = TOP + max(len(v) for v in cols.values()) * (H + GY) + 10
        out = [f'<svg class="depgraph" xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
               f'viewBox="0 0 {width} {height}" role="group" aria-labelledby="gtitle">'
               '<title id="gtitle">Dependency graph of the book\'s results, one column per chapter</title>'
               '<defs><pattern id="hatch" patternUnits="userSpaceOnUse" width="6" height="6" '
               'patternTransform="rotate(45)"><rect width="6" height="6" class="gn-hatch-bg"/>'
               '<line x1="0" y1="0" x2="0" y2="6" class="gn-hatch-line"/></pattern>'
               '<marker id="arrow" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" '
               'orient="auto-start-reverse"><path d="M0,0 L8,4 L0,8 z" class="gn-arrow"/></marker></defs>']
        for ci, ch in enumerate(chapters):
            x = LEFT + ci * (W + GX)
            out.append(f'<text x="{x}" y="22" class="gn-col">Chapter {esc(ch)}</text>')
        # edges first (under nodes): dependency -> result that cites it
        for n in self.data["nodes"]:
            for u in n["uses"]:
                if u["target"] != "node" or u["id"] not in pos:
                    continue
                (x1, y1), (x2, y2) = pos[u["id"]], pos[n["id"]]
                y1c, y2c = y1 + H / 2, y2 + H / 2
                if x1 == x2:
                    bend = W + 18 + min(60, abs(y2 - y1) / 8)
                    d = f"M{x1 + W},{y1c} C{x1 + bend},{y1c} {x2 + bend},{y2c} {x2 + W},{y2c}"
                elif x1 < x2:
                    d = f"M{x1 + W},{y1c} C{x1 + W + GX / 2},{y1c} {x2 - GX / 2},{y2c} {x2},{y2c}"
                else:
                    d = f"M{x1},{y1c} C{x1 - GX / 2},{y1c} {x2 + W + GX / 2},{y2c} {x2 + W},{y2c}"
                out.append(f'<path d="{d}" class="gn-edge" data-from="{attr(u["id"])}" data-to="{attr(n["id"])}" '
                           f'marker-end="url(#arrow)"/>')
        for n in self.data["nodes"]:
            x, y = pos[n["id"]]
            title = (f'{long_name(n)} {n["labels"][0] if n["labels"] else ""} — statement: '
                     f'{STATEMENT_WORDS[n["statement_status"]]}; proof: {PROOF_WORDS[n["proof_status"]]}'
                     f'{"; proved as printed, and every result it cites (unreviewed TeX references) also proved as printed" if n["printed_with_cited_printed"] else ""}'
                     f'{"; " + ", ".join(n["issues"]) if n["issues"] else ""}')
            mark = "✕ " if n["proof_status"] == "refuted" else ""
            node = (f'<g class="gn {fill_class(n)} gn-st-{n["statement_status"]}" data-id="{attr(n["id"])}">'
                    f'<title>{esc(title)}</title>'
                    f'<rect x="{x}" y="{y}" width="{W}" height="{H}" rx="4"/>'
                    f'<text x="{x + W / 2}" y="{y + 15}">{esc(mark + short_name(n))}</text></g>')
            out.append(f'<a href="#n-{attr(n["id"])}">{node}</a>')
        out.append("</svg>")
        return "".join(out)

    def dot(self) -> str:
        lines = ["// Generated by site/build.py from the node graph; render with: dot -Tsvg graph.dot",
                 "digraph results {", "  rankdir=LR; node [shape=box, fontsize=10];"]
        style = {"printed": "solid", "corrected": "dotted", "restricted": "dashed", "refuted": "bold",
                 "partial": "dashed", "implied": "dotted", "explanatory": "dotted", "cited-out-of-scope": "dashed",
                 "open": "solid", "prose-claim": "dotted"}
        color = {"printed": "darkgreen", "corrected": "darkgoldenrod", "restricted": "purple", "refuted": "red",
                 "partial": "darkorange", "implied": "steelblue", "explanatory": "gray",
                 "cited-out-of-scope": "sienna", "open": "gray", "prose-claim": "gray"}
        fill = {"gn-pf-fully": "darkgreen", "gn-pf-proved": "palegreen", "gn-pf-variant": "honeydew",
                "gn-pf-refuted": "mistyrose", "gn-pf-open": "white"}
        for n in self.data["nodes"]:
            st = n["statement_status"]
            fc = fill_class(n)
            lines.append(f'  "{n["id"]}" [label="{short_name(n)}", style="filled,{style[st]}", color={color[st]}, '
                         f'fillcolor={fill[fc]}{", fontcolor=white" if fc == "gn-pf-fully" else ""}];')
        for n in self.data["nodes"]:
            for u in n["uses"]:
                if u["target"] == "node":
                    lines.append(f'  "{u["id"]}" -> "{n["id"]}";')
        lines.append("}")
        return "\n".join(lines) + "\n"

    def graph_page(self) -> str:
        legend_border = "".join(
            f'<li><svg width="46" height="20" aria-hidden="true"><g class="gn gn-pf-open gn-st-{k}">'
            f'<rect x="2" y="2" width="42" height="16" rx="3"/></g></svg> {esc(STATEMENT_WORDS[k])}</li>'
            for k in STATEMENT_WORDS)
        legend_fill = "".join(
            f'<li><svg width="46" height="20" aria-hidden="true"><g class="gn {c} gn-st-open">'
            f'<rect x="2" y="2" width="42" height="16" rx="3"/></g></svg> {esc(w)}</li>'
            for c, w in (("gn-pf-fully", "Proved as printed, and every result it cites through TeX cross-references "
                                         "(unreviewed) is also proved as printed; not a reviewed proof-dependency check"),
                         ("gn-pf-proved", "Proved as printed; some result it cites is not proved as printed"),
                         ("gn-pf-variant", "Proved only in corrected or restricted form (hatched)"),
                         ("gn-pf-refuted", "Printed statement refuted in Lean and nothing proved (also marked ✕)"),
                         ("gn-pf-open", "Not proved")))
        trs, last = [], None
        for n in self.data["nodes"]:
            if n["chapter"] != last:
                last = n["chapter"]
                trs.append(f'<tr class="ch-row"><th colspan="6">Chapter {esc(last)} '
                           f'{self.chapter_title(last)}</th></tr>')
            link = self.href(n)
            name = esc(long_name(n))
            name = f'<a href="{attr(link)}">{name}</a>' if link else name
            lab = f'<div class="label"><code>{esc(n["labels"][0])}</code></div>' if n["labels"] else ""
            st = f'<span class="gstatus">{esc(STATEMENT_WORDS[n["statement_status"]])}</span>'
            if n.get("implied_variant"):
                st += f'<div class="label">from a {esc(n["implied_variant"])} entry</div>'
            pf = esc(PROOF_WORDS[n["proof_status"]]) + (" · cited results also printed*" if n["printed_with_cited_printed"] else "")
            uses = ", ".join(
                f'<a href="#n-{attr(u["id"])}">{esc(short_name(self.nodes[u["id"]]))}</a>'
                for u in n["uses"] if u["target"] == "node")
            ctx = [u for u in n["uses"] if u["target"] == "context"]
            if ctx:
                uses += (", " if uses else "") + f'{len(ctx)} definition/algorithm reference{"s" if len(ctx) > 1 else ""}'
            lean = " ".join(f'<code title="{attr(e["name"])}">{esc(e["name"].rsplit(".", 1)[-1])}</code>'
                            for e in n["statement_entries"])
            issues = " ".join(f'<span class="cid">{esc(c)}</span>' for c in n["issues"])
            search = " ".join([long_name(n), n["labels"][0] if n["labels"] else "", lean,
                               " ".join(n["issues"])]).lower()
            trs.append(f'<tr id="n-{attr(n["id"])}" data-status="{attr(n["statement_status"])}" '
                       f'data-search="{attr(re.sub("<[^>]+>", "", search))}">'
                       f'<td>{name}{lab}<div class="label">{self.tex_link(n)}</div></td>'
                       f'<td>{st}</td><td>{pf}</td><td class="lean-names">{lean}</td><td>{issues}</td>'
                       f'<td>{uses or "—"}</td></tr>')
        chips = "".join(f'<button type="button" class="chip" data-filter="{k}">{esc(w)}</button>'
                        for k, w in STATEMENT_WORDS.items())
        s = self.data["summary"]
        body = f"""<h1>Dependency graph</h1>
<div class="incomplete" role="note"><strong>INCOMPLETE.</strong> This graph shows the reviewed status of each
source result; it does not certify a chapter or the book. Arrows are <strong>unreviewed</strong> candidates read
from the TeX cross-references (<code>\\ref</code>, <code>\\eqref</code>, …) inside each result and its proof: a
reference may be a comparison rather than a dependency, and a real dependency may be cited without one. There are
{s["uses_edges"]} such edges and {s["uses_edges_reviewed"]} reviewed ones.</div>
<p class="lede">One node per numbered theorem, lemma and claim ({s["named_results_in_inventory"]}), plus remarks and
the displayed claims that a statement-index entry or the coverage ledger cites ({s["prose_nodes"]}). Two axes:
the <strong>border</strong> shows which statement is in Lean, the <strong>fill</strong> shows whether it is proved.
Every status is also written in words in the table below. Arrows point from a cited result to the result that
cites it. Click a node for its row; each row links to the book text. <a href="status.html">Counts by chapter</a> ·
<a href="graph/nodes.json">nodes.json</a> · <a href="graph/graph.dot">graph.dot</a> (Graphviz).</p>
<div class="glegend"><div><h2>Border: statement</h2><ul>{legend_border}</ul></div>
<div><h2>Fill: proof</h2><ul>{legend_fill}</ul></div></div>
<div class="graph-wrap">{self.svg()}</div>
<h2>All nodes</h2>
<div class="filters"><input type="search" id="q" placeholder="Search number, label, Lean name or C-id" aria-label="Search nodes">
<div class="chips"><button type="button" class="chip on" data-filter="">All</button>{chips}</div></div>
<div class="table-wrap"><table class="results graph-table"><thead><tr><th>Item</th><th>Statement in Lean</th>
<th>Proof</th><th>Statement entries</th><th>Source issues</th><th>Cites (unreviewed)</th></tr></thead>
<tbody>{''.join(trs)}</tbody></table></div>
<p class="lede">* “Cited results also printed” means every result this one cites through TeX cross-references
(unreviewed) is also proved as printed. It is not a reviewed proof-dependency check. Definitions, assumptions and
algorithms are context, not nodes; references to them are counted but never block.</p>"""
        return self.site.shell(f"Dependency graph · {self.site_title()}", body, "graph", toc=False)

    def errata_page(self) -> str:
        """Source issues and Lean refutations, generated from SOURCE-ISSUES.md and the node graph."""
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

        refuted = [n for n in self.data["nodes"] if n["refutations_cited"]]
        rrows = "".join(
            f'<tr><td>{node_link(n)}<div class="label"><code>{esc(n["labels"][0] if n["labels"] else "")}</code></div></td>'
            f'<td>{" ".join(f"<code>{esc(x)}</code>" for x in n["refutations_cited"])}</td>'
            f'<td>{esc(STATEMENT_WORDS[n["statement_status"]] if n["proof_status"] == "proved" else "Nothing proved")}'
            f'{"" if n["proof_status"] != "proved" else " proved"}</td>'
            f'<td>{lean.issue_links([c[1:] for c in n["issues"] if c[1:] in lean.issue_slugs])}</td></tr>'
            for n in refuted)
        crows = []
        for cid, info in sorted(lean.issue_slugs.items(), key=lambda kv: int(kv[0])):
            ns = by_issue.get(f"C{cid}", [])
            items = ", ".join(f'{node_link(n)} ({esc(status_phrase(n))})' for n in ns)
            crows.append(f'<tr><td><a href="{attr(issues_url)}#{attr(info["slug"])}">C{esc(cid)}</a></td>'
                         f'<td>{esc(re.sub(r"^(Candidate )?C[0-9]+: *", "", info["title"]))}</td>'
                         f'<td>{items or "—"}</td></tr>')
        rev = lean.git.rev
        body = f"""<h1>Errata and source issues</h1>
<div class="incomplete" role="note"><strong>Candidates, not confirmed errata.</strong> Every item below was found
by independent reviews performed by AI agents against the pinned TeX of arXiv:2610.41903v1. None has been confirmed
by the authors or refereed by a human mathematician. A Lean refutation is a machine-checked proof that the printed
statement, <em>under the reading the project formalized</em>, is false; the reading itself is part of what a reader
should check.</div>
<p class="lede">Generated at build time from <code>docs/SOURCE-ISSUES.md</code>, the coverage ledger and the
named-result ledger at commit <code>{rev[:10]}</code>. The curated record with effects on each result is
<a href="{attr(lean.git.blob("docs/ERRATA-AND-DEVIATIONS.md"))}">docs/ERRATA-AND-DEVIATIONS.md</a>.</p>
<h2>Printed statements refuted in Lean</h2>
<p class="lede">Source items whose coverage-ledger row or named-result ledger record cites a Lean theorem named
<code>not_…_printed…</code> (the project convention). Each refutation is of the printed statement under the reading
formalized; the card and the coverage row say which reading. Some other source issues are refuted in Lean under other names or only on paper; see
the full list below and the record above.</p>
<div class="table-wrap"><table class="results"><thead><tr><th>Item</th><th>Lean refutation</th>
<th>What is proved instead</th><th>Source issue</th></tr></thead><tbody>{rrows}</tbody></table></div>
<h2>All source-issue candidates ({len(crows)})</h2>
<p class="lede">Each links to its entry in SOURCE-ISSUES.md, which states the evidence and any proposed correction.
“Results” lists the tracked source results whose ledger rows cite the issue.</p>
<div class="table-wrap"><table class="results"><thead><tr><th>Id</th><th>Candidate</th><th>Results</th></tr></thead>
<tbody>{"".join(crows)}</tbody></table></div>"""
        return self.site.shell(f"Errata · {self.site_title()}", body, "errata", toc=False)

    def nodes_json(self) -> str:
        return gen_nodes.dumps(self.data)

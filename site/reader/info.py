"""Overview-level pages that are not book text: methodology, credits, contribute, book contents, About stub.

A mixin of `render.Site`. Every count comes from the node-graph summary (`Site.cnt`); every version fact
(commit, Lean toolchain, Mathlib revision, source hashes) is read from the pinned revision at build time.
"""

from __future__ import annotations

import html

from .lean import LABELS, MARKERS, REPO, gen_nodes

ARXIV = "https://arxiv.org/abs/2610.41903v1"
MAINTAINER = "aaradhyapandeycs"
MAINTAINER_URL = "https://github.com/aaradhyapandeycs"


def esc(t) -> str:
    return html.escape(str(t), quote=False)


def attr(t) -> str:
    return html.escape(str(t), quote=True)


class InfoPages:
    # ------------------------------------------------------------------ book contents
    def book_landing_page(self) -> str:
        chapters, cur = [], None
        for p in self.pages:
            if p.level == 0:
                cur = {"page": p, "sections": []}
                chapters.append(cur)
            elif cur:
                cur["sections"].append(p)
        items = []
        for ch in chapters:
            p = ch["page"]
            c = self.summary["by_chapter"].get(p.chapter or "", {})
            counts = ""
            if c.get("named_total"):
                counts = ", ".join(f'{self.cnt(f"by_chapter.{p.chapter}.named_by_label.{k}")} {esc(LABELS[k][0])}'
                                   for k in gen_nodes.SITE_LABEL_ORDER if c["named_by_label"][k])
                counts = f'<span class="ch-count">{counts}</span>'
            secs = "".join(f'<li><a href="{s.id}.html"><span class="secnum">{esc(s.number or "")}</span> {s.title}</a></li>'
                           for s in ch["sections"])
            items.append(f'<li><h2><a href="{p.id}.html"><span class="secnum">{esc(p.number or "")}</span> {p.title}</a></h2>'
                         f'{counts}<ol class="sections">{secs}</ol></li>')
        body = f"""<h1>The book</h1>
<p class="lede"><em>{esc(self.book.provenance.get("title", ""))}</em>, by {esc(self.authors_text())}
(<a href="{ARXIV}">arXiv:2610.41903v1</a>), rendered from the pinned TeX with the book's own numbering and notation.
Counts after each chapter are its numbered results by label.</p>
<ol class="book-toc">{"".join(items)}
<li><h2><a href="acknowledgements.html">Acknowledgements</a></h2></li><li><h2><a href="references.html">References</a></h2></li></ol>"""
        return self.shell(f"Book · {self.book.provenance.get('title', '')}", body, "book", toc=False)

    # ------------------------------------------------------------------ methodology
    def methodology_page(self) -> str:
        rev = self.lean.git.rev
        prov = self.book.provenance
        tar = prov["artifacts"].get("2610.41903v1.tar", "")
        pdf = prov["artifacts"].get("2610.41903v1.pdf", "")
        ci = (f'<p>This build was made by the publishing workflow after the “Lean and source checks” workflow '
              f'succeeded on this commit: <a href="{attr(self.ci_run_url)}">that CI run</a>.</p>'
              if self.ci_run_url else "")
        audit = (f'<p>Axiom-audit output of that run: <code>{esc(self.audit_line)}</code></p>'
                 if self.audit_line else "")
        checks = (f'<a href="{attr(self.ci_run_url)}">the CI run that gated this build</a>' if self.ci_run_url
                  else f'<a href="{REPO}/commit/{rev}">the CI checks shown for this commit on GitHub</a>')
        no_audit = (f'<p>This build records no axiom-audit output of its own. The evidence for this commit is the '
                    f'“Lean and source checks” workflow (<code>.github/workflows/lean.yml</code>): it runs '
                    f'<code>lake build</code> on the whole project and then <code>python3 scripts/check.py</code>, which '
                    f'compiles the import closure and runs <code>Audit.lean</code>, failing on any axiom other than '
                    f'<code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code> in any '
                    f'<code>StatisticalRL</code> declaration. See {checks}.</p>')
        out_of_scope = [n for n in self.node_data["nodes"] if n["statement_status"] == "cited-out-of-scope"]
        oos = "".join(f'<li><a href="{attr(self.href(n) or "#")}">{esc(n["display_name"])}</a></li>' for n in out_of_scope)
        mapping = [
            ("stated", "Numbered result with a reviewed record whose Lean statement is the printed one (no "
                       "<code>_corrected</code>/<code>_restricted</code> suffix); or a remark/display whose "
                       "coverage-ledger row records it as proved as stated."),
            ("corrected", "A <code>_corrected</code> entry is proved; it links a source issue saying what differs."),
            ("restricted", "A restricted entry (for example positive sample sizes, closed half-spaces, a smaller "
                           "algorithm class) is proved. A result that is both corrected and restricted gets this "
                           "label with an “also corrected” marker."),
            ("incomplete", "Everything else: printed statement refuted with nothing proved, partial, implied by "
                           "another entry (not separately proved), cited from the literature and out of scope, only "
                           "supporting Lean statements without a reviewed record, a related statement proved instead of "
                           "the printed one, or nothing formalized yet. The small text after the label gives the reason."),
        ]
        rows = "".join(f'<tr><td><span class="status {LABELS[k][1]}">{esc(LABELS[k][0])}</span></td><td>{d}</td></tr>'
                       for k, d in mapping)
        body = f"""<h1>Methodology and verification</h1>
<nav class="page-toc"><a href="#sources">Sources and scope</a> · <a href="#formalized">How results are formalized</a> ·
<a href="#review">Review</a> · <a href="#verify">Verification snapshot</a> · <a href="#establishes">What compilation establishes</a> ·
<a href="#reproduce">Reproduce</a> · <a href="#labels">Status labels</a> · <a href="#rendering">Rendering</a></nav>

<h2 id="sources">Sources and scope</h2>
<p>The book is the pinned arXiv source of <em>{esc(prov.get("title", ""))}</em> (arXiv:{esc(prov.get("arxiv_id", ""))}),
restored and hash-checked by <code>scripts/fetch_source.py</code>: source archive SHA-256 <code>{esc(tar)}</code>,
PDF SHA-256 <code>{esc(pdf)}</code> (from <code>source/provenance.json</code>). The site follows the
<code>StatisticalRL-nowplain.tex</code> variant, so material marked arXiv-only is omitted. The goal is every chapter,
appendix, stated result, algorithm and substantive claim. Numbering, labels and line ranges come from
<code>docs/source-inventory.json</code>, a lexical checklist that certifies nothing. Excluded by a dated project
decision (results the book cites from the literature without stating them about its own objects):</p>
<ul>{oos or "<li>none</li>"}</ul>

<h2 id="formalized">How results are formalized</h2>
<p>Each source result proved in some form has a statement entry in <code>Formalization/Statements/ChN.lean</code>: a
<code>Prop</code> named after the result (for example <code>Thm3_2</code>), self-contained, with every hypothesis
written out, and a docstring citing the source label and <code>.tex</code> lines. A separate
<code>ChNProofs.lean</code> proves each entry by applying a library theorem (<code>Thm3_2_holds : Thm3_2</code>). A
corrected or restricted statement carries the suffix <code>_corrected</code> or <code>_restricted</code> and points to
an entry in <code>docs/SOURCE-ISSUES.md</code>. A source error is an open obligation: it is recorded with the evidence
and a proposed correction, and the corrected statement is never called the original theorem. All corrections and
refutations are {esc("proposed by this project; not confirmed by the authors")}.</p>
<p>Where the book cites a result from the literature or omits its proof, the Lean proof is new; where it follows the
book's argument, it formalizes an existing proof. The ledger field <code>proof_origin</code> records which; the
<span class="marker mk-new-proof">{esc(MARKERS["new-proof"])}</span> marker appears only where it says so.</p>

<h2 id="review">Review</h2>
<p>Builder agents write definitions and proofs; separate critic agents reconstruct the source mathematics and try
to refute each translation. A builder never certifies its own statement. All reviewers are AI agents (Claude, by
Anthropic) working under the maintainer's direction: no result has been refereed by a human mathematician or approved
by the authors. The reviews are recorded in the ledgers (<code>docs/named-result-status.json</code>,
<code>docs/COVERAGE.md</code>) and linked from each card.</p>
<p><strong>Five-bin statement audit.</strong> Every statement entry and its wrapper were audited against the pinned TeX
(<a href="{attr(self.lean.git.blob("docs/statement-audit/README.md"))}">audit of 2026-11-09/10</a>): each binder and
hypothesis is put in exactly one bin, SOURCE (a premise of the printed statement), STANDING (a standing assumption of
the chapter), TYPING (type formation), DISCLOSED (a deviation named by the suffix, stated in the docstring and recorded
in SOURCE-ISSUES) or EXCESS. Any EXCESS fails the entry, as does any deviation in an unsuffixed entry. The audit's own
totals are a dated record; see the linked file. Cards link the batch report that covers them.</p>
<p><strong>Definition audit.</strong> A later audit (2026-11-10) checked the bodies of the project definitions that
statement entries use, not only their signatures: indexing, normalization, off-domain branches (zero counts, singular
matrices, division by zero) and choice functions. The conventions it found are disclosed in
<a href="{attr(self.lean.git.blob("docs/SOURCE-ISSUES.md"))}#statement-index-scope-disclosures">SOURCE-ISSUES.md,
“Statement-index scope disclosures”</a>.</p>

<h2 id="verify">Verification snapshot</h2>
<table class="facts"><tbody>
<tr><th>Commit</th><td><a href="{REPO}/tree/{rev}"><code>{rev}</code></a></td></tr>
<tr><th>Lean toolchain</th><td><code>{esc(self.toolchain())}</code> (from <a href="{attr(self.lean.git.blob("lean-toolchain"))}"><code>lean-toolchain</code></a>)</td></tr>
<tr><th>Mathlib</th><td><a href="https://github.com/leanprover-community/mathlib4/tree/{attr(self.mathlib_rev())}"><code>{esc(self.mathlib_rev())}</code></a> (from <a href="{attr(self.lean.git.blob("lake-manifest.json"))}"><code>lake-manifest.json</code></a>)</td></tr>
<tr><th>Source archive</th><td>SHA-256 <code>{esc(tar)}</code></td></tr>
<tr><th>Built</th><td>{esc(self.built)}</td></tr>
</tbody></table>
{ci}{audit or no_audit}
<p>Publishing: the site's workflow (<code>.github/workflows/pages.yml</code>) deploys automatically only after the
“Lean and source checks” workflow (<code>lean.yml</code>: Lean build and <code>python3 scripts/check.py</code>, which
includes the axiom audit) has succeeded on a push to <code>main</code>, builds exactly that commit, and deploys only
while it is still the tip of <code>main</code>. A maintainer can also start a deploy by hand from <code>main</code>;
that path does not wait for the Lean workflow. The footer links the CI status of the commit each page was built from
(<a href="{REPO}/commit/{rev}">this commit</a>).</p>

<h2 id="establishes">What compilation establishes, and what it does not</h2>
<p>It establishes that each exported Lean theorem is proved from Mathlib and the three axioms <code>propext</code>,
<code>Classical.choice</code> and <code>Quot.sound</code>: no <code>sorry</code>, no project axioms
(<a href="{attr(self.lean.git.blob("Audit.lean"))}"><code>Audit.lean</code></a> collects the transitive axioms of every
declaration in the <code>StatisticalRL</code> namespace and fails on any other).</p>
<p>It does <strong>not</strong> establish that a Lean statement means what the book says (that is the job of the
reviews and the statement audit), that the project's definitions model the book's objects (the definition audit),
that prose the project has not formalized is correct, or that the book is complete. A label on this site is a
ledger record, not a certificate of a chapter or of the book.</p>

<h2 id="reproduce">Reproduce</h2>
<pre class="cite">git clone {REPO}.git
cd statistical-foundations-rl-lean
git checkout {rev}
python3 scripts/fetch_source.py  # restore and hash-check the arXiv source
lake exe cache get               # prebuilt Mathlib
lake build                       # compile the formalization
lake env lean Audit.lean         # transitive axiom audit
python3 scripts/check.py         # import closure and axiom audit, as in CI</pre>
<p>Expected: the build succeeds with no <code>sorry</code>, and the audit ends with its line
“Axiom audit passed for … project declarations.”, giving the number of declarations it checked at that commit
(this page does not record that number unless the publishing workflow supplied the CI log). A statement is then checked by reading its entry in <code>Formalization/Statements/ChN.lean</code>
(each card links it) against the TeX beside it.</p>

<h2 id="labels">Status labels</h2>
<p>Every source item gets exactly one of four labels, computed by <code>scripts/gen_nodes.py</code> from the ledgers
and published in <a href="graph/nodes.json">graph/nodes.json</a>; this site reads the label from there and never
classifies on its own. Counts never become a percentage of the book.</p>
<div class="table-wrap"><table class="results"><thead><tr><th>Label</th><th>Meaning</th></tr></thead><tbody>{rows}</tbody></table></div>
<p>Markers after a label: <span class="marker mk-refuted">{esc(MARKERS["refuted"])}</span> when a Lean theorem
refutes the printed statement under the reading formalized, shown even when a corrected form is proved;
<span class="marker mk-fails-paper">{esc(MARKERS["fails-paper"])}</span> when there is no Lean refutation but a paper
argument by this project (not checked in Lean) shows that the printed statement fails. Both come from the explicit
ledger field <code>printed_refuted</code> in <code>docs/named-result-status.json</code>, which states the reading and
the Lean theorems; the generator fails if a Lean refutation cited elsewhere in the ledgers is missing from it; <span class="marker mk-new-proof">{esc(MARKERS["new-proof"])}</span> when the ledger records
an own proof where the book cites or omits one; <span class="marker mk-also-corrected">{esc(MARKERS["also-corrected"])}</span>
on a restricted result that is corrected too. Items the coverage ledger reviews as making no mathematical claim
(attribution, notation) carry no label and are left out of every count. Algorithms, assumptions and definitions carry
no label: a Lean entry that cites them does not make them proved.</p>

<h2 id="rendering">Rendering</h2>
<p>A small converter turns the TeX into HTML and leaves the math to MathJax&nbsp;3.2.2, with the book's own macros.
Equation numbers come from the inventory. Each theorem-like block has a “TeX source” disclosure with its exact
lines. PDF figures were converted to PNG; figure numbers are computed per chapter. <code>site/check_fidelity.py</code>
compares the site's prose with the hash-pinned PDF in both directions and checks that every formula in the TeX appears
on the site; <code>site/check_macros.py</code> checks that no TeX macro reaches a reader unrendered.</p>"""
        return self.shell(f"Methodology · {self.book.provenance.get('title', '')}", body, "methodology", toc=False)

    # ------------------------------------------------------------------ credits
    def credits_page(self) -> str:
        prov = self.book.provenance
        authors = "".join(f"<li>{esc(a)}</li>" for a in prov.get("authors", []))
        body = f"""<h1>Credits and citation</h1>
<h2>The book</h2>
<p><em>{esc(prov.get("title", ""))}</em>, <a href="{ARXIV}">arXiv:{esc(prov.get("arxiv_id", ""))}</a>, by</p>
<ul class="people">{authors}</ul>
<p>Licensed <a href="{attr(prov.get("license_url", "https://creativecommons.org/licenses/by/4.0/"))}">{esc(prov.get("license", "CC BY 4.0"))}</a>.
Changes were made: converted from the pinned TeX to HTML, comments and author-only material removed, math typeset by
MathJax. The authors have not reviewed and do not endorse this formalization; every correction and refutation on
this site is proposed by this project and not confirmed by them.</p>
<h2>The formalization</h2>
<ul>
<li><strong>Maintainer and code contributor:</strong> <a href="{MAINTAINER_URL}">{MAINTAINER}</a> on GitHub: direction of
the project, review decisions and scope decisions. All contributors: <a href="{REPO}/graphs/contributors">GitHub
contributors</a>.</li>
<li><strong>AI assistance:</strong> the Lean definitions and proofs, the reviews recorded in the ledgers and this
website were produced with Claude (Anthropic) under the maintainer's direction.</li>
</ul>
<h2>Tools and prior work</h2>
<ul>
<li><a href="https://lean-lang.org/">Lean 4</a> (<code>{esc(self.toolchain())}</code>) and
<a href="https://github.com/leanprover-community/mathlib4">Mathlib</a> (revision <code>{esc(self.mathlib_rev()[:12])}</code>).</li>
<li><a href="https://www.mathjax.org/">MathJax</a> 3.2.2 typesets the mathematics.</li>
<li><a href="https://github.com/scottnarmstrong/LeanAutoformalizationSkills">Scott Armstrong's LeanAutoformalizationSkills</a>
(CC BY 4.0; the pinned revision is recorded in the repository README), the
<a href="https://github.com/leanprover/skills">Lean team's skills</a> and
<a href="https://github.com/cameronfreer/lean4-skills">Cameron Freer's Lean skills</a>.</li>
<li>Design inspiration: Axiom's <a href="https://stacks.axiommath.ai/">Stacks Project in Lean</a>, and the PFR,
Equational Theories and Carleson project sites. No code is shared with them.</li>
</ul>
<h2 id="cite">How to cite</h2>
<p>The book:</p>
<pre class="cite">{esc(self.bibtex_book())}</pre>
<p>This formalization (incomplete; cite the commit you used):</p>
<pre class="cite">{esc(self.bibtex_repo())}</pre>
<h2>Licences</h2>
<p>Book text and figures: CC BY 4.0, attributed to the authors (changes as described above). Lean code and this
site: Apache-2.0. The skill collections and other third-party material keep their own licences. Publisher
formatting files from the arXiv archive are not republished.</p>"""
        return self.shell(f"Credits · {prov.get('title', '')}", body, "credits", toc=False)

    # ------------------------------------------------------------------ contribute
    def contribute_page(self) -> str:
        body = f"""<h1>Contribute</h1>
<p class="lede">Corrections from readers are the most useful contribution: a Lean statement that does not say what the
book says, a misread hypothesis, a wrong label, or a rendering error.</p>
<h2>Report a misreading</h2>
<p>Open an issue at <a href="{REPO}/issues">{esc(REPO.split("//", 1)[1])}/issues</a> with:</p>
<ul><li>the source item (number and label, for example Theorem 7.11, <code>thm:Berry-Esseen-linear</code>) and its
<code>.tex</code> lines (shown on every card);</li>
<li>the Lean entry (for example <code>Thm7_11_corrected_halfspace</code>) and the commit shown in the page footer;</li>
<li>what is wrong, and what the book says instead.</li></ul>
<h2>Build and check</h2>
<pre class="cite">python3 scripts/fetch_source.py
lake exe cache get
lake build
lake env lean Audit.lean
python3 scripts/check.py
python3 scripts/gen_nodes.py --check
python3 site/build.py --rev HEAD
python3 site/check_fidelity.py
scripts/run_before_push.sh</pre>
<h2>Project rules</h2>
<ul>
<li>No <code>sorry</code>, <code>admit</code> or custom axioms; the transitive axioms of every project declaration
are only <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>.</li>
<li>Theorem signatures are preserved during proof work: no hidden hypotheses, weakened conclusions or unproved
intermediate inputs.</li>
<li>Every result recorded as proved gets a self-contained <code>Prop</code> entry in
<code>Formalization/Statements/ChN.lean</code> and a <code>_holds</code> wrapper in <code>ChNProofs.lean</code>.</li>
<li>A source error is an open obligation: corrected or restricted entries carry the suffix and point to
<code>docs/SOURCE-ISSUES.md</code>; the corrected statement is never called the original.</li>
<li>Builders do not certify their own statements; an independent critic reviews each one. The full rules are in
<a href="{attr(self.lean.git.blob("AGENTS.md"))}"><code>AGENTS.md</code></a>.</li>
</ul>
<h2>Open work</h2>
<p>Open items are listed in <a href="{attr(self.lean.git.blob("docs/NEXT.md"))}"><code>docs/NEXT.md</code></a>
(generated) and in the results index under the <a href="results.html#f=incomplete&amp;all=1">incomplete</a> label.</p>"""
        return self.shell("Contribute · Statistical Foundations of RL in Lean", body, "contribute", toc=False)

    # ------------------------------------------------------------------ about (moved)
    def about_page(self) -> str:
        body = """<h1>About this site</h1>
<p>The contents of this page moved. Old links keep working through the sections below.</p>
<h2 id="status">How status works</h2>
<p>See <a href="methodology.html#labels">Methodology: status labels</a> and <a href="methodology.html#review">review</a>.</p>
<h2 id="verify">Check it yourself</h2>
<p>See <a href="methodology.html#verify">Methodology: verification snapshot</a> and
<a href="methodology.html#reproduce">reproduce</a>.</p>
<h2 id="cite">How to cite</h2>
<p>See <a href="credits.html#cite">Credits and citation</a>.</p>"""
        return self.shell("About · Statistical Foundations of RL in Lean", body, "about", toc=False)

# Book reader: design and plan

Status: **first version built, not published.** The reader lives in
[`site/`](../site/README.md) and builds to the git-ignored `site/_build/`.
It renders the whole book (all chapters) with Lean statements and proofs
beside the results. Nothing is committed or deployed. The monograph
formalization is incomplete; the reader shows what exists and says so.

Goal: a static website that shows each result of arXiv:2610.41903v1 next to
its Lean statement-index entry, with an honest status, exact source locators
and pinned links, generated entirely from files already in this repository.

## 1. Inspiration

Axiom's [Stacks Project in Lean](https://stacks.axiommath.ai/) site (inspected
2026-11-05). What was observed there:

- A **Library** view: search box, a book-ordered tree (chapter → section →
  tag) with counts, and a detail pane for the selected tag. The tag is in the
  URL (`/library?tag=0023`), so every view can be shared.
- The detail pane gives the tag, kind, a status word, chapter and section, and
  three buttons: the upstream book page, the dependency graph, and the
  **Lean source pinned to a commit with a line range**. Below them is the Lean
  code with original line numbers and one tab per declaration. Identifiers
  link to Mathlib's doc-gen4 pages. The code carries an attribute
  `@[stacks 0023 "…"]` that ties it to the tag.
- Status words with a legend: Formalized, In Mathlib, Partial, Conditional,
  Not applicable, Needs correction. A tag without Lean code says
  "No Lean declaration carries this tag."
- Book statements are stored as HTML with inline TeX and typeset in the
  browser by MathJax 3.2.2 with XyJax, next to the attribution line
  "Statement from the Stacks project, GNU FDL".
- A static front end reads prebuilt JSON (a library index, a search index, a
  summary with the Lean commit and build time, one file per tag) from a CDN.
- A dependency graph (treemap and "city" layouts) distinguishes Lean
  dependencies from natural-language citations.

The fuller record is in the personal Claude skill `lean-book-reader-design`
(`references/axiom-stacks-observations.md`). Nothing in this plan depends on
Axiom's code; only the ideas are borrowed.

## 2. Data sources (all read-only to the reader)

| Source | What the reader takes from it |
| --- | --- |
| `source/upstream/tex/` (ignored; restore with `python3 scripts/fetch_source.py`) | Statement text by file and line range; macros from `chapters/commands.tex` |
| `source/provenance.json` | SHA-256 of every source file. The build fails if a restored file does not match |
| `docs/source-inventory.json` | One entry per environment: id, labels, kind, printed number, title, chapter, section path, file and lines, text hash. Also `labels` and `references` (cross-references and citations) |
| `Formalization/Statements/ChN.lean` | Statement-index entries (`Prop` definitions). Each docstring cites a label such as `lem:Freedman-prelim` and a range such as `chapters/prelim.tex:1056–1075`. Name suffixes mark variants (`_corrected`, `_positiveN` and similar) |
| `docs/named-result-status.json` | `certified_named_results` and `proved_variants`: the reviewed status, evidence file and scope for each entry |
| `docs/COVERAGE.md` | Reviewed scope text and "Partial" components that have no statement entry yet |
| `docs/SOURCE-ISSUES.md` | Candidate issues (C1, C2, …) linked from corrected and restricted entries |
| git | The commit the site describes; used for every Lean link |

Rules: the reader derives everything from these files and hardcodes no counts.
It never edits them and never runs Lean. When two sources disagree, the page
shows the disagreement rather than choosing one.

## 3. Status model

Order of evidence, strongest first. Each page shows one or more of these.

| Status | Rule |
| --- | --- |
| Proved as printed | Entry in `certified_named_results` |
| Proved in corrected form | Entry in `proved_variants`, name contains `corrected`; show the printed statement, the proved statement and the source-issue link |
| Proved for a restricted case | Entry in `proved_variants`, any other variant suffix; state the restriction |
| Partial | `COVERAGE.md` lists components but no statement entry exists |
| Open source issue | Only a `SOURCE-ISSUES.md` record exists |
| Not yet formalized | Everything else (the default) |

A statement entry with no ledger record is shown as "Statement entry exists;
no reviewed status is recorded", never as proved. A site-wide banner states
that the formalization is incomplete and that statuses do not certify a
chapter or the book. Chapter pages show counts by status for labelled results,
computed at build time, and say what the count leaves out (prose claims,
algorithms, unlabelled displays). No percentages. The rules are written up
in the personal skill `lean-proof-status-display`.

## 4. Mapping labels to Lean entries

A build step in the proposed `site/build.py` (§8), separate from `scripts/`:

1. Parse each `ChN.lean` (not `*Proofs.lean` or `*Definitions.lean`) as text:
   docstring, `def Name : Prop :=` and the body up to the next blank line.
   Labels are backticked tokens with a colon; ranges match
   `path.tex:start–end` with or without backticks, en dash or hyphen.
2. Join on label to `source-inventory.json`, normalizing
   `chapters/x.tex` to `source/upstream/tex/chapters/x.tex`.
3. Validate: the label exists; the cited range covers the inventory's
   environment range (a wider range with context is fine); the source file
   hash matches provenance; the ledger's `lean_statement` names an existing
   entry.
4. Write `data/map.json` with the source version, Lean commit, all pairs,
   unmapped entries and validation findings.

A dry run of this parser on the current working tree (2026-11-05) found
entries whose docstrings cite no label (for example `Lemma3_3`,
`Thm5_2_corrected`), entries whose label is a display equation rather than the
environment, and one range that starts a line after its environment
(`Lemma5_3`, 639 versus 638). These are reader-side findings to triage with the
statement-index owner, not corrections; this plan does not edit those files.
Unlabelled source results (such as Lemma 2.1) need the inventory id or the
status file's `source_inventory_id` as their key.

The general method is in the personal skill `lean-source-label-mapping`.

## 5. Book text: TeX to HTML

Recommended route, in two stages:

1. **Statement extraction + KaTeX** (as in the prototype). Cut the
   environment by the inventory's line range, drop comment-only lines and
   `\label`, turn `equation` into display math, keep math as TeX and typeset
   it in the browser with KaTeX auto-render (or pre-render at build time with
   the `katex` CLI for faster pages). Feed `commands.tex` macros to KaTeX.
   Resolve `\ref{…}` and `\cite{…}` through the inventory's `labels` and
   `references` tables into in-site links and bibliography keys. Keep a
   "TeX source" disclosure with the exact lines and file hash.
2. **Whole chapters later** with LaTeXML (`latexmlc`) using a plain `book`
   class instead of the publisher's `nowfnt.cls`, so chapter prose,
   numbering and cross-references render. plasTeX (the leanblueprint route) is
   the alternative if a Python-only toolchain is preferred.

MathJax 3 is the fallback if KaTeX rejects macros the book uses (it supports
more LaTeX); Axiom uses MathJax. Test the worst displays first: aligned
multi-line bounds in the online-RL chapter and algorithm environments.
Algorithms (`algorithm` environments in the inventory) need their own renderer or should be shown as TeX source.

## 6. Lean statements

Stage 1, **source text**: show each entry's docstring and `def` with original
line numbers, read from the file at the pinned commit (the prototype warns
when the working tree differs from the commit). Link to
`https://github.com/aaradhyapandeycs/statistical-foundations-rl-lean/blob/<sha>/<file>#L<a>-L<b>`
and to the matching `…_holds` proof in `ChNProofs.lean`.

Stage 2, **doc-gen4**: generate API docs for the `Formalization` library in a
separate CI job at the release commit and link each name to
`Formalization/Statements/ChN.html#StatisticalRL.Statements.Name`, and
identifiers in the code to their declarations, as Axiom does. This needs a
build, so it runs only in CI with the project's normal pinned toolchain,
never on a shared local checkout.

Stage 3, **hover** (optional): SubVerso/Verso-style highlighted code with
type information. Only if stages 1–2 prove useful.

## 7. Pages and URLs

- `/` overview: what the site is, the incomplete-status banner, links to
  `COVERAGE.md` and the statement index, the pinned versions.
- `/chapters/<n>/`: book-ordered list of every inventory result in the
  chapter with its status word; statuses counted, not summed into a
  percentage.
- `/r/<label-or-id>/`: one page per result (the prototype's layout): book
  statement left, Lean entries right, status, source and Lean links,
  scope text from the ledger, source-issue links, and "cited by" from the
  inventory's cross-references.
- `/issues/`: corrected and restricted results with their source-issue
  records.
- Search: a prebuilt JSON index over labels, printed numbers, titles and
  Lean names, searched in the browser.
- Later: a dependency view built from inventory cross-references (book
  dependencies) and, separately, Lean imports; never merged into one graph
  without saying which edge is which.

One HTML file per result keeps GitHub Pages deep links working without a
single-page fallback.

## 8. Hosting and build

- Build: a Python script (proposed `site/build.py`) that reads the files in
  §2 and writes `site/_build/` (HTML, `data/*.json`, copied assets). No Lean.
- Host: GitHub Pages from a workflow artifact
  (`actions/upload-pages-artifact` + `actions/deploy-pages`), triggered on
  release tags or manually, never on every push. The workflow restores the
  source with `python3 scripts/fetch_source.py`, which verifies hashes,
  then runs the build. The built output is not committed.
- Pin CDN scripts to exact versions (KaTeX 0.16.11 in the prototype) or
  vendor them.
- Footer on every page: book version, Lean commit, build time, ledger files
  read.

## 9. Licensing

- The book is CC BY 4.0. Every page quoting it carries: authors, title,
  arXiv id and link, licence link, "changes were made" (comments removed,
  re-typeset), and that the authors do not endorse the formalization. The
  site may quote statements and, under the same licence, chapter text.
- **Do not publish** the publisher formatting files in the arXiv archive
  (`nowfnt.cls`, `nowfnt-biblatex.sty`, `nowfnt-listofjournals.cfg`,
  `NOWFnT-data.tex`, logo PDFs) or the archive itself; link to arXiv instead.
  The build reads TeX at build time and emits only HTML.
- Figures from the book are CC BY 4.0 too, but convert and attribute each one
  individually, or link to the PDF instead.
- Repository code is Apache-2.0 (`LICENSE`); the site's own code and design
  follow it.

## 10. Prototype

A local, git-ignored proof of concept is at `.local/book-reader-prototype/`.
`build.py` renders one inventory label (default `lem:Freedman-prelim`, Lemma
2.9) beside its statement-index entry, derives the status from
`named-result-status.json`, checks the TeX hash against provenance and the
docstring range against the inventory, and writes `index.html` and
`map.json`. Run:

```bash
python3 -I .local/book-reader-prototype/build.py --label lem:Freedman-prelim
```

It was checked in a browser on 2026-11-05: the statement typesets with
KaTeX, the Lean entry shows with original line numbers, and the page warns
because `Ch2.lean` differs from the last commit in the working tree. It is not
for publication.

## 11. Plan and what remains

1. Agree on the status model (§3) and the key for unlabelled results, with
   the ledger owners.
2. Triage the mapping findings in §4 with the statement-index owner.
3. Promote the prototype into `site/build.py` with all labels, chapter
   pages and search; add `\ref`/`\cite` resolution.
4. Independent review of a sample of generated pages against the TeX and the
   Lean files, by someone who did not write the builder.
5. GitHub Pages workflow (manual trigger first).
6. doc-gen4 links, then whole-chapter LaTeXML rendering, then a dependency
   view.

Open questions: whether to show chapter prose or statements only at first;
whether partial `COVERAGE.md` components get their own pages; how to show
results that map to several Lean entries with different statuses.

# Book reader

A static website that shows the whole of *Statistical Foundations of
Reinforcement Learning* (arXiv:2610.41903v1), rendered from its pinned TeX,
with the project's Lean statements and proofs next to the results they
formalize. Inspired by Axiom's [Stacks Project in Lean](https://stacks.axiommath.ai/)
site; no code is shared with it. Design notes: [docs/BOOK-READER-PLAN.md](../docs/BOOK-READER-PLAN.md).

The formalization is incomplete, and the site says so on every page.

## Build

```bash
python3 scripts/fetch_source.py   # restore and hash-check the pinned arXiv TeX
python3 site/build.py             # writes site/_build/ (git-ignored)
python3 -m http.server -d site/_build 8000
```

`build.py --rev <commit>` selects the Lean revision. The default is the
upstream branch (normally `origin/main`), so every Lean link points at a
commit that exists on GitHub. `--lean-repo <clone>` reads Lean files and
ledgers from another clone; use it when this checkout's git objects are slow
to read (for example, offloaded by iCloud). Python 3.9+ standard library
only; `pdftoppm` (Linux) or `sips` (macOS) converts the book's PDF figures.
No Lean or Lake process runs. A build is written beside `_build/` and
swapped in at the end, so a failed build never removes the served site.

## Fidelity check

```bash
python3 site/check_fidelity.py
```

Independent of the converter: it compares the site's prose with the text of
the hash-pinned arXiv PDF in both directions, and checks that every formula
in the TeX appears verbatim on the site. It exits non-zero on any
difference and runs in the publishing workflow.

## Keeping the site current

```bash
python3 site/watch.py --lean-repo <clone of the project>
```

Fetches `origin` every two minutes and rebuilds as soon as new commits reach
`main`. On GitHub, `.github/workflows/pages.yml` builds and checks the site on
every push that touches Lean files, ledgers or the reader, but deploys only
after the "Lean and source checks" workflow has succeeded on a push to `main`
(triggered by `workflow_run`, building exactly that commit, and only while it
is still the tip of `main`), or on a manual run on `main`. The footer of every
page links the CI status of the commit it was built from.

## What it reads (never writes)

| Input | Used for |
| --- | --- |
| `source/upstream/tex/` (verified against `source/provenance.json`) | Book text, macros, bibliography, figures |
| `docs/source-inventory.json` | Theorem, equation and section numbers; labels; line ranges |
| `Formalization/Statements/ChN.lean` at the Lean revision | Statement entries, matched by the source labels and `.tex` ranges in their docstrings |
| `Formalization/Statements/ChNProofs.lean`, library files | The `_holds` proofs and the library theorems they apply |
| `docs/named-result-status.json`, `docs/COVERAGE.md`, `docs/SOURCE-ISSUES.md` | Status, scope text, review records, source-issue links |

Lean files and ledgers are read with `git show <rev>:<path>`, so
uncommitted work in the checkout never appears on the site.

## One inventory for every count and label

Every status word and every number on the site comes from the node graph that
`scripts/gen_nodes.py` derives from the ledgers at the same Lean revision
(`docs/graph/nodes.json`: `nodes[].site_label`, `site_markers`,
`site_sub_reason`, `display_name`, and the `summary`). The reader never
classifies a status on its own and holds no hand-written status text: notes
shown on cards come from the ledger fields `display_note` (per record) and
`entry_display_notes` (per statement entry without a record).

- Four labels: *proved as stated*, *proved with corrections*, *proved under
  restrictions*, *incomplete* (with a sub-reason). Markers: *✕ printed statement
  refuted* (ledger kind `counterexample`: a non-degenerate case under the natural
  reading), and the qualified markers, never counted as refuted: *∂ boundary case*
  (`"kind": "boundary"`: only a degenerate point, such as a single action),
  *◇ reading-dependent* (`"reading"`), *⊘ outside the assumed domain* (`"domain"`),
  *∅ ill-posed* (`"ill-posed"`: the printed formula is undefined and Lean's value is a
  convention), *⚠ appears to fail (paper argument)*, *new proof* (only where
  `proof_origin` is an own proof), *also corrected*. Explanatory items (no mathematical claim) get no label and are left
  out of every count; algorithms, assumptions and definitions get no label.
- A ledger record with `"status_override": "incomplete"` never counts as proving
  its item (downgrade only; any other value fails the generator).
- Every count on a page is written as
  `<span class="n" data-count="summary.path">N</span>`; `site/build.py` fails if
  any shown number differs from the summary, or if the summary's label counts
  differ from a direct tally of the nodes. It also fails if a link into the
  repository at the pinned commit names no file (for example a directory) or a
  `#anchor` that the linked Markdown file does not define (an `<a id>` or a
  heading slug); see `site/reader/links.py` and `scripts/tests/test_site_links.py`.
- `status.html` (counts by chapter), `graph.html` (graph with a
  numbered-results-only view, chapter filter and click highlight of cited and
  citing results, plus a table of every node) and `errata.html` (refuted printed
  statements, corrections, restrictions, repaired proof gaps, all candidates) are
  generated from the same data; `graph/nodes.json` and `graph/graph.dot` are
  published beside them. Edges are unreviewed candidates from TeX
  cross-references, and the pages say so.
- Check the committed `docs/graph/nodes.json` and `docs/NEXT.md` with
  `python3 scripts/gen_nodes.py --check` (run by `scripts/run_before_push.sh`).

## Pages

Overview (`index.html`) → Results (`results.html`) → Book (`book.html` and the
chapter pages) → Status (`status.html`, `graph.html`, `errata.html`) →
`methodology.html`, `contribute.html`, `credits.html`. `about.html` keeps its
old anchors (`#status`, `#verify`, `#cite`) as pointers to the new pages.
`build.py --ci-run-url <url>` adds a sentence naming the Lean CI run that gated a
deploy, and `--audit-log <file>` prints that run's axiom-audit line verbatim;
both are omitted for local builds. Without `--ci-run-url` the Methodology page
says the build records no gating CI run and that the commit's Lean CI status
(linked) may still be pending. The workflow passes `--ci-run-url` only when the
checked-out commit's `build.py --help` lists it, since `workflow_run` uses the
default branch's workflow file with an older commit's `build.py`.

## Placement rules

Each Lean card is shown at the source item it formalizes: the inventory entry
of its ledger record, else the node `gen_nodes.py` attaches it to (a cited
label inside the docstring's first `.tex` range, else that range). Only an
entry with no such item falls back to the first block it cites. Every other
block an entry cites (an algorithm, assumption, definition or display) shows
a "cited by" link and no status chip; algorithms, assumptions and definitions
never carry a status. The build fails if a ledger record's card is not at its
own source item. A card whose item is a display inside an algorithm (or
another context item) is shown in a row of its own right after that block,
which links to it.

`check_fidelity.py` looks for PDF words in the book text of the site; its
whole-site fallback search also skips the Lean column, since Lean code is not
book text and its words (`theorem`, `probability`, ...) would otherwise
capture the in-order search.

## Layout

- `build.py`: entry point, count check against the node-graph summary, and build
  report (labels, unhandled TeX, unresolved references, unplaced Lean entries)
- `check_fidelity.py`, `tools/pdftext.swift`: fidelity check against the PDF and TeX
- `watch.py`: rebuild whenever `origin/main` moves
- `reader/tex.py`: TeX → HTML; math left as TeX for MathJax 3.2.2, equation
  numbers inserted from the inventory
- `reader/book.py`: source verification, macros, bibliography, figures, pages
- `reader/lean.py`: Lean entries, proofs, exports, Lean cards and status chips
- `reader/render.py`: pairing, book pages, overview and results index
- `reader/info.py`: methodology, credits, contribute, book contents, About stub
- `reader/graph.py`: status dashboard, dependency graph and generated errata page
- `static/`: CSS and small scripts

## Publishing

Published at <https://aaradhyapandeycs.github.io/statistical-foundations-rl-lean/>
by `.github/workflows/pages.yml`. An automatic deploy happens only after the
"Lean and source checks" workflow has succeeded on a push to `main`, builds
exactly that commit, and deploys only while it is still the tip of `main`; a
manual run on `main` also deploys, without waiting for the Lean workflow.
`site/_build/` contains `.nojekyll`. The book text is CC BY 4.0 with
attribution on every page, and the publisher's formatting files are never
copied.

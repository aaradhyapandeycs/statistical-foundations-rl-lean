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
`main`. On GitHub, `.github/workflows/pages.yml` rebuilds and republishes on
every push to `main` that touches Lean files, ledgers or the reader, once
GitHub Pages is enabled.

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

## Status rules

A status comes only from the reviewed ledger. A statement entry with no
ledger record is shown as "no reviewed status recorded", never as proved.
Corrected and restricted variants are never shown as the printed result,
even when the ledger certifies them. Results with nothing in Lean say
"Not yet formalized". See the site's About page for the full legend.

## Layout

- `build.py`: entry point and build report (unhandled TeX, unresolved
  references, unplaced Lean entries)
- `check_fidelity.py`, `tools/pdftext.swift`: fidelity check against the PDF and TeX
- `watch.py`: rebuild whenever `origin/main` moves
- `reader/tex.py`: TeX → HTML; math left as TeX for MathJax 3.2.2, equation
  numbers inserted from the inventory
- `reader/book.py`: source verification, macros, bibliography, figures, pages
- `reader/lean.py`: Lean entries, proofs, exports, ledger status
- `reader/render.py`: pairing and page templates
- `static/`: CSS and small scripts

## Checks done when this was built (2026-11-05)

- All 1077 inventory labels and every numbered environment and proof have anchors.
- All 41 statement entries at commit `2015162` were placed next to book text,
  and all their library theorems were located.
- Every formula on every page parsed in MathJax with the book's macros (0 errors).
- `check_fidelity.py`: every prose passage on the site is found in the arXiv
  PDF and every passage of the PDF's main text is found on the site; all
  3148 formulas in the TeX appear verbatim. It found one real defect (the
  caption of Figure 3.2), which was fixed.
- An independent read-only review compared a sample of results across
  chapters 2–7 with the TeX, all equation numbers and cross-references with
  the inventory, and all Lean code blocks with `git show`; it found no text,
  math or status errors. Its six layout and indexing findings were fixed.

## Publishing

Not published. GitHub Pages can serve `site/_build/` (it contains
`.nojekyll`). Publishing needs the maintainer's approval; the book text is
CC BY 4.0 with attribution on every page, and the publisher's formatting
files are never copied.

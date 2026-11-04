# Statement-index verification

The backfill contains 16 source-facing proposition definitions and 16 proofs
applying the existing exports: two in Chapter 2, six in Chapter 3, seven in
Chapter 4, and one corrected UCBVI optimism entry in Chapter 5. Both chapter
files are imported from `Formalization.lean`. The status ledger names each
statement and proof; its 15 original-result certifications are unchanged and
the corrected optimism variant is recorded separately.

`Lemma4_8` states the printed global learning-rate hypothesis. Its wrapper
restricts that hypothesis to the prefix needed by the existing exports. The
incorrect C11 finding was removed. Existing positive-sample, causal-selector,
and zero-count limitations are disclosed in the statements and source-issues
ledger.

## Validation

- Command: `python3 scripts/check.py`, run on a clean snapshot of the staged
  backfill, with fresh project build artifacts and the pinned dependency
  artifacts reused without rebuilding them.
- Result: **passed**, 403 project modules, including the actual
  `Formalization` root and `Audit`.
- Transitive axiom audit: **passed for 4720 project declarations**, allowing
  only `propext`, `Classical.choice`, and `Quot.sound`.
- A focused probe resolved all 16 ledger definition/proof names and inspected
  their proof axioms; all reported only those three permitted axioms.
- Independent source review: [critic-statement-index-backfill.md](critic-statement-index-backfill.md).
  Its pinned statement/definition/proof hashes match the published sources.
- Definition extractions preserve the existing mathematical objects; the
  changed implementation files preserve the existing theorem/lemma command
  text. No library theorem was weakened or reproved for the index.
- Evidence run: `verification/20261104T012201873051Z/manifest.json` (local ignored
  evidence directory); manifest SHA-256 `be52af60fcc9c3671004e78cb4158209e241de38933f6634cf50642a40811758`.
- Aggregate Lean-source hash-map SHA-256: `430e5c9e441c93c16c72c42c67c2ef944f06daf22c326fe79823ceba4a307f0a`. Every staged Lean
  source was checked against this successful run before publication.

An earlier snapshot run was deliberately interrupted while two Chapter 3
wrapper elaboration errors were repaired. It is not passing evidence; the
successful run above rebuilt the complete final backfill. Compiler linter
warnings remain and did not fail the check. Dependency pins are unchanged.
The separate in-progress TD theorem files were excluded from this commit and
from this clean validation snapshot.

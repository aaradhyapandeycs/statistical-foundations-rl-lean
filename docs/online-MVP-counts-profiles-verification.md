# MVP profile and stored-count verification

Pinned source: arXiv:2610.41903v1, `chapters/onlineRL.tex` SHA-256
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.
Lemma 5.11 is `lemma:key2`, lines 1540–1542, using the profile definition
at 1506–1525. Lemma 5.12 is `lem:sum-inv-Nhk-mvp`, lines 1570–1577.

- Exports: `StatisticalRL.OnlineRL.MVPProfile.sourceMVPFinitePossibleProfiles_card_bound_all`
  and `StatisticalRL.OnlineRL.onlineMVP_operationalHistory_sourceCountBudget`.
- Full statements: `StatisticalRL.Statements.Lemma5_11` and `Lemma5_12_powerOfTwo_corrected`;
  applying proofs have the `_holds` suffix. Their direct project imports
  are definition modules only; the proof imports stay in Ch5Proofs.
- The profile theorem keeps the source K-budget and exact cardinality bound.
  It counts all finite state-action row tables, including every actual trace,
  and proves cumulative/operational count agreement, threshold index bounds,
  ceiling-family inclusion and K=1. The arbitrary row-table form is stronger
  than the source algorithm-only conclusion. C15 identifies the printed
  intermediate rounding gap; the final bound is unchanged.
- The stored-count theorem retains K≥2, k-outer/h-inner sum order,
  pre-episode table timing, max-one denominator and factor4 bound.
  It uses cumulative totals, per-successor pending counts and completed
  batch sizes under the prose's power-of-two trigger interpretation.
  Arbitrary chronological state-action/successor traces include the source
  dyadic algorithm. C13 records the inconsistent literal trigger and invalid
  factor-two step; the actual proof
  uses dyadic blocks. No concentration or policy premise is assumed.
- Qualified checks: ten count-provider modules and eight actual exports;
  three profile providers plus both standalone statement snippets and eight
  actual exports; then both full Chapter 5 index files and their twelve
  actual proof exports. Only standard axioms are allowed. The full-index
  focused run stages 667 unchanged baseline modules and 13 qualified
  providers, excluding the old index/facade/Audit, so it is not a full
  integration claim.
- Guarded affected integration passed **17 rebuilt+
  667 verified reused=684 project modules**, auditing **6,658
  declarations** with only propext, Classical.choice and Quot.sound.
- Run: `20261104T164753717003Z`.
- Manifest SHA-256: `11af38f998dde2681657c78e8540595596555098a2bd58292ad12b3d5b1ec923`.
- Driver SHA-256: `bd87289009ebf57c3b0efd91ec957308b6104a63f21daf86fc05732fbac2f7b8`.
- Statement SHA-256: `c1f3bc6ce785003eb40af0a92843abe3fcafe9b4d70df4d1e331bddcf8fc9b1d`.
- Proof-index SHA-256: `9c0505863ceb77656d22795050faa98506c9cc223c6742d344ce01ac8b6795e7`.

The executed local check is the guarded affected-check driver using the
pinned Lean wrapper and repository checker/parser. It is not a fresh clean
`python3 scripts/check.py` run over all 684 files. Verified reuse ancestry is
684→671→668→666→659→566→520→513→477→453→447→438→clean418. Current source/OLean
hashes, all retained ancestry edges, compiler/package paths and metadata
were checked. Historical clean418 did not pin OLean/package bytes; later
reuse receipts bind those artifacts. Public full-checkout commands remain
`lake build` and `lake env lean Audit.lean`; local full checking uses
`python3 scripts/check.py`. CI results are reported separately when complete.

Project size: 74,861 Lean lines including comments/blanks in 684 files.
Ledger: 20 original named entries with existing disclosures plus eight
corrected variants. This does not certify MVP uniform concentration, the
MVP regret theorem, an entire chapter or the monograph.

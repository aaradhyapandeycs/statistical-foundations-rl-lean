# Complete corrected T2/T3/T4 verification

Source: arXiv:2610.41903v1, `lem:bound-T234`,
`chapters/onlineRL.tex:988–1005`. Chapter SHA-256:
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

- Actual export: `StatisticalRL.OnlineRL.onlineSourceAllocated_actualT234_K2_strict`.
- Complete statement: `StatisticalRL.Statements.Lemma5_8_K2_corrected`.
- Applying proof: `StatisticalRL.Statements.Lemma5_8_K2_corrected_holds`.
- All four displayed inequalities concern one actual law/event. The printed
  iota and threshold are retained. The scope is K≥2, the C8 finite zero-count
  convention and analysis charge H, the fixed deterministic maximizing tie
  rule, and the source confidence/bonus domains. See SOURCE-ISSUES C8/C12.
- Qualified focused checks passed for 46 new modules (T2: 9, T3: 9,
  shared/T4: 25, joint: 3), together with actual export axiom probes.
  The complete Chapter 5 index and applying proof then passed; six actual
  statement proofs were probed with only standard axioms.
- The guarded affected integration completed with exit 0: **50 rebuilt plus
  516 verified reused modules**, covering all **566 project modules**.
- The whole-library audit passed for **5,811 declarations**, allowing only
  `propext`, `Classical.choice` and `Quot.sound`.
- Run: `20261104T120329467897Z`.
- Manifest SHA-256:
  `8de596578d0a288d673d2064cd959d42877dca03ca0eacf4ae90d48181ed4170`.
- Guarded affected-check driver SHA-256:
  `32aa88afe4db33f56bc4aa32a543a6059140981d15320b4ee6dea652bcad51dd`.
- Chapter 5 statement SHA-256:
  `13de3a0e0c693eee9e658d46e1c551c9799bff2bdd22141967457eb0dfcc8c6b`.
- Chapter 5 proof SHA-256:
  `b82700e1adc91bccb5cfdc2ea66ee5cf70eea5da124a3224a9c1d667dcaa17d2`.

The executed command was the guarded `check_affected.py` integration driver,
using the repository checker/parser and pinned Lean wrapper. It rebuilt the
complete reverse-import closure and ran the full Audit. This is not a fresh
clean `python3 scripts/check.py` run over 566 modules. Public fresh-checkout
commands remain `lake build` and `lake env lean Audit.lean`; local complete
checking uses `python3 scripts/check.py`.

Reuse ancestry is 566 → 520 → 513 → 477 → 453 → 447 → 438 → clean418.
All current source/artifact hashes and retained ancestry edges were checked,
with the same resolved compiler/package locations and dependency metadata
unchanged before/after. The historical clean418 record did not pin OLean or
package bytes; inherited artifacts are bound by the later TV438 reuse receipts.
Separately, the previous public 520-module GitHub CI run 41821883698 passed
the full build, inventory checks and `scripts/check.py` audit.

The applying index wrapper emits one nonfatal pinned-Mathlib deprecation
warning for `Set.setOf_app_iff`; its proof and axiom audit pass. No warnings
are suppressed. Earlier failed focused attempts were retained separately;
the terminal qualified joint run is 5 and statement run is 1 of version 2.

Project size: **64,724 Lean lines** including blanks/comments in **566 files**.
The ledger retains 18 original named entries with existing disclosed limits,
plus four corrected variants. This release does not establish T5/T6, final
online regret, any complete chapter, or the complete monograph.

# Printed inverse-visit count verification

Source: arXiv:2610.41903v1, Lemma 5.3, `lem:sum-inv-Nhk-ucbvi`,
`chapters/onlineRL.tex:638–646`. Chapter SHA-256:
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

- Actual export: `StatisticalRL.OnlineRL.onlineSequential_maxOne_reciprocal_count_budget`.
- Statement: `StatisticalRL.Statements.Ch5.Lemma5_3`.
- Applying proof: `StatisticalRL.Statements.Ch5.Lemma5_3_holds`.
- The denominator is the printed max(N,1), including first-visit mass;
  K≥2 and the source sum order are preserved. The arbitrary finite planner/
  path formulation generalizes the printed algorithm-specific counting
  claim. No bonus, confidence or unproved rank estimate is assumed.
- Focused qualification run08 passed both providers, a six-export provider
  probe, Ch5/Ch5Proofs and a nine-export statement-proof probe. Only the
  standard axioms appeared. Earlier failed attempts remain uncounted;
  run07 had all Lean steps pass but failed its old Python postcheck, so
  only run08's corrected complete sentinel supports qualification.
- Guarded affected integration: **6 rebuilt+662 verified reused=668**
  modules; the full audit covers **6,460 declarations** and permits only
  `propext`, `Classical.choice`, `Quot.sound`.
- Run: `20261104T152700260157Z`.
- Manifest SHA-256: `2cfa753ec3e937d68fc926659e9bae7131607d1bcaeb69aa67979ab9a831e542`.
- Driver SHA-256: `a407dea09cdb10e04073594982bd8db73f3e72ba06700c1584a169058e5e35bc`.
- Statement SHA-256: `c3e44794c8d46828bddfaa3e6f6c5a27c69e3c56595368ef14430a0a29970758`.
- Applying proof SHA-256: `09cfd97bbdc9d0eb0458189fa47c7f78db57185db5a69d30fbe0044712b5ca9c`.

The executed command was the guarded affected-check driver, using the
project's checker/parser and pinned Lean wrapper. This is not a new clean
`python3 scripts/check.py` run across 668 modules. Reuse ancestry is
668→666→659→566→520→513→477→453→447→438→clean418. Current source/OLean hashes,
ancestry edges and compiler/package paths/metadata were checked. The old
clean418 record did not pin OLean/package bytes; later receipts bind those
inherited artifacts. Public full-checkout commands remain `lake build` and
`lake env lean Audit.lean`; local full checking uses `python3 scripts/check.py`.

Size: 73,339 project Lean lines including comments/blanks in 668 files.
Ledger: 19 original named entries with disclosed limits plus six corrected
variants. This does not certify a whole chapter or the whole monograph.

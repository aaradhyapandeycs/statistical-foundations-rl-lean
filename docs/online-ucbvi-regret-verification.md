# Corrected UCBVI main theorem verification

Source: arXiv:2610.41903v1, Theorem 5.2, `thm-ucbvi-regret`,
`chapters/onlineRL.tex:472–482`; proof closure 1112–1153; iota 726–734.
Pinned chapter SHA-256:
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

- Actual export: `StatisticalRL.OnlineRL.onlineUCBVI_actual_regret_high_probability`.
- Full statement: `StatisticalRL.Statements.Thm5_2_corrected`.
- Applying proof: `StatisticalRL.Statements.Thm5_2_corrected_holds`.
- Explicit rate 20(√(SAH³K)+S²AH³)(1+iota), fixed universal bonus constants 4,16,
  all K≥1 and 0<δ<1. The producer's strict probability bound implies the
  printed at-least1−δ form. Regret is true optimal-minus-selected-policy
  value at the actual reset states; no event/variance estimate is a premise.
- Scope: finite zero-count algorithm completion (C8), fixed deterministic
  maximizing tie rule; iid initial resets and causal sequential transitions.
  K=1 and small-K branches are deterministic; large-K uses the actual
  unconditional T0/T56 producers and explicit scalar closure.
- Seven freshly qualified modules and a strict ten-export axiom probe passed.
  The combined full Chapter 5 statement/proof files and eight actual statement
  proof exports then passed focused compilation and the axiom probe.
- Guarded affected integration: **11 rebuilt+655 verified reused=666**
  project modules; full axiom audit **6,443 declarations**, allowing only
  `propext`, `Classical.choice`, `Quot.sound`.
- Run: `20261104T143612216885Z`.
- Manifest SHA-256: `104ff5105977167d1d9b5641111f6460b8d7728433327b9705ca6f7d1d382678`.
- Driver SHA-256: `9d849aa6fa72b4ce610e16c7f703b3ad85534b31f696f7e216d9ada5a2b1b64d`.
- Statement SHA-256: `8f1dbb2dac9dfa504513985c219ac255d7a3e8e00f55d68b7542f606a732d726`.
- Applying proof SHA-256: `ed84ada595d2ab2cb530f6aca4516fbcc40e8e3b6ef42329775c047ea13c9ab5`.

This used the guarded affected-check driver and the project's pinned Lean
wrapper/checker parser. It is not a new clean `python3 scripts/check.py` run
across 666 modules. Reuse ancestry is666→659→566→520→513→477→453→447→438→clean418;
all current source/OLean hashes, retained ancestry edges and compiler/package
paths/metadata were checked. The historical clean418 record did not pin
OLean/package bytes; later receipts bind those inherited artifacts.
Public fresh-checkout commands remain `lake build`, `lake env lean Audit.lean`;
local full checking uses `python3 scripts/check.py`.

Project size: 73,062 Lean lines including comments/blanks in 666 files.
The ledger has 18 original named entries with disclosed limits plus six
corrected variants. This theorem does not certify the literal undefined
zero-count algorithm, other chapter 5 algorithms, a whole chapter or monograph.

# Independent review: corrected randomized Q-risk theorem

## Exact sources and audit

The final wrapper and its reconstruction bridge match the builder handoff:

- `.local/GenerativeLowerBoundQMixtureFinalRandomized.lean`, SHA-256 `a4bc1dae5f190955e12a345d39ce74041e24fcdd3bd7c515a9595012e47d69b8`.
- `.local/GenerativeLowerBoundQRandomReconstruct.lean`, SHA-256 `2b3368a89fc42a4b952bf9ca4378ad8949c1a83d4d2ee2c419d39c17fa95238a`.

I independently rebuilt the exact 40-module deterministic Q-mixture closure and the 10-module randomized extension in `.local/q-mixture-final-randomized-fresh-audit`, after checking every source hash against the pinned manifest. Lean compiled all 50 modules. A generated audit module ran `#print axioms` over 205 declarations; the final wrapper, the reconstruction-event transfer, and the other theorem exports used only `propext`, `Classical.choice`, and `Quot.sound` (one non-theorem declaration reported no axioms). No `sorryAx` or other nonstandard axiom appeared. Lean emitted only unused-variable/style linter warnings, including the known unused `hsize`.

Reproduction script: `.local/audit-q-mixture-final-randomized-fresh.sh`.

## Statement and semantic review

`qMixtureSource_randomized_Q_risk` quantifies one kernel `κ` from the complete actual sample array to probability measures on real Q arrays. `κ` is chosen before the existential family index, and its probability-measure condition holds for every data array. Thus the theorem covers arbitrary measurable randomized Q estimators, including output laws with infinite support; it does not cover model-dependent kernels.

The conclusion selects an actual source-family MDP and bounds the joint sample/output probability from below by `1/4` for the strict event `ε < ‖Qhat − Q*‖`, where `Q*` is that MDP's optimal-policy trajectory expected-Q array. The Borel event is proved measurable in the final wrapper. The proof transfers this event through the common reconstruction map, then applies baseline-versus-uniform-mixture risk selection. It uses actual full-array sampling, with N independent draws for every state/action row; deterministic absorber rows are part of the full array and are reconstructed from the active observation. The common output kernel is composed with this same model-independent reconstruction for each mixture law.

The stated dimensions are `m ≥ 1`, `A ≥ 2`, and `(m+1)A ≥ 16`, so the source MDP has at least two states and two actions. The `SA ≥ 16` premise is retained but unused by this proof. The parameter regime and budget are `γ ∈ [2/3,1)`, `0 < ε < 1/[32(1−γ)]`, and `512 N(1−γ)^3 ε² ≤ log((m+1)A)`. `N=0` is included: the sample space is the singleton empty array, the budget is satisfied, and the reconstruction/output-kernel argument remains well-typed. The family selection uses the already proved strict baseline-to-each-alternative Q separation greater than `2ε`; it does not rely on pairwise separation among alternatives.

## Limits

This verifies the corrected randomized Q-estimation claim for the staged source and its exact staged dependency closure. It is not a production integration check. The theorem intentionally carries explicit nondegenerate state/action assumptions and should not be read as validating a version of the printed source theorem that omits them.

Production integration: the reviewed source body compiles in the project export with qualified imports; the Q-learning causality file has been given the production module name `QLearningCausality`. The full project check audited 2,755 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.

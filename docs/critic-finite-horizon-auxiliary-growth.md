# Independent review: finite-horizon auxiliary variance growth

Reviewed staged source `.local/FiniteHorizonAuxiliaryGrowth.lean`, SHA-256 `9df2d4d8bbeaf8ca5f9c47d66e6e06c85d161a90fb65082530b8eccb5a9bd1c3`. The source-level comparator is Li et al., [*Breaking the Sample Size Barrier in Model-Based Reinforcement Learning with a Generative Model*, arXiv:2005.12900v8](https://arxiv.org/pdf/2005.12900v8), Lemma 12, PDF p. 34, equation (112), proved in Appendix C.2, PDF pp. 37–38; see also `docs/source-finite-horizon-h3-proof-map.md`. No compiler was run for this review.

## Semantic check

The growth module imports the actual `FiniteHorizonAuxiliaryVariance` recursion and defines its budget from the true selected transition row's variance of the actual next-suffix level-l value, plus the true-row expectation of the suffix budget. This is the population conditional variance in Li et al.; there is no empirical transition variance or independently supplied variance sequence. The recurrence and proof are for one fixed deterministic nonstationary policy, consistent with the auxiliary sequence definition.

The source's terminal convention is exact: the empty remaining-stage list gives zero budget and zero auxiliary value at every level. A list of length H represents H remaining stages, and the level-zero induction uses the environment's actual reward constraints `0≤r≤1` to prove value at most H. The successor-level induction is over all natural levels, with no truncation or added growth hypothesis. The theorem bounds every state pointwise; `norm_trueAuxiliaryValueAt_le_source_growth` converts nonnegativity into the complete finite-state supremum-norm statement for every stage suffix, including the terminal suffix.

The main argument has the same structure as Appendix C.2: `auxiliaryVarianceBudget_le_potential` telescopes the accumulated conditional variances against the potential `2 M V−V²`; `auxiliaryVarianceBudget_le_sq` bounds that budget by `M²`; `trueAuxiliaryValue_succ_sq_le` combines the current conditional variance with the next-level second moment via Jensen and finite Cauchy–Schwarz. The final induction proves precisely `V_l≤H(√(3H))^l`, the displayed Lemma 12 bound. The factor 3 is a valid slack factor in the final square-root step; it is not introduced as an assumption.

## Stronger internal consequence

The two proved helpers `auxiliaryVarianceBudget_le_sq` and `trueAuxiliaryValue_succ_sq_le` imply the sharper one-step estimate

`V_{l+1}(s)^2 ≤ length(es) · M^2`

whenever every level-l suffix value is at most M and its suffix variance budget is therefore at most `M²`. With nonnegative values this gives the factor `√H` in place of `√(3H)` in the level induction. Thus the final theorem deliberately exposes Li et al.'s stated constant rather than the strongest consequence of its helpers. This is a consequence of the checked lemmas, not a separately exported sharper all-level theorem in this module.

## Scope

The module proves the source growth estimate only. It does not establish Lemma 9's Bernstein premise, a simultaneous probability event, the C.1 recursive unrolling, or the end-to-end H³ theorem.

## Independent exact-source compile and axiom evidence

The exact reviewed sources were copied to a fresh project-owned directory and compiled sequentially: first `FiniteHorizonAuxiliaryVariance.lean` to `.local/finite-horizon-growth-independent-gzwtBv/out/FiniteHorizonAuxiliaryVariance.olean` using `bash scripts/lean-local.sh -o ...`, then `FiniteHorizonAuxiliaryGrowth.lean` against that fresh artifact with the pinned `.local/lean` and the same existing project/Mathlib import paths. Both compilation logs are empty (no diagnostics). A separate probe imported the freshly compiled growth module and ran `#print axioms` for all 33 exported definitions/theorems across both modules (23 recursion exports and 10 growth exports). Every result used only `propext`, `Classical.choice`, and `Quot.sound`. No dependency rebuild or production integration build was performed. Source hashes remained `19f843f138314e21a14d5b29eef88e758add4389dbbcfa7eb225e496bc68d4ee` for the recursion and `9df2d4d8bbeaf8ca5f9c47d66e6e06c85d161a90fb65082530b8eccb5a9bd1c3` for the growth module.

Production integration: the reviewed source bodies compile in the project export, with qualified imports. In the seeded two-point risk module only, two local instance names were renamed to prevent collisions; the theorem statement and proof are unchanged. The full project check audited 2,373 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.

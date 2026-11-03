# Staged model-based policy-evaluation construction

`.local/ModelBasedPolicyEvaluation.lean` builds the actual policy-row experiment and plug-in value estimator for Chapter 3's model-based policy-evaluation algorithm. It does **not** assert or assume its statistical guarantee. This is staged evidence requiring independent review and integration.

## Source and scope

The source (`generative_model_model_based.tex:78–130`, `alg:policy-eval-model-based`) draws N independent samples from each policy-induced transition row `Pπ(·|s)`, forms their empirical frequencies, and outputs `(I−γ P̂π)⁻¹ rπ`. Its Theorem `thm:model-based-policy-eval` (`:140–156`) asserts uniform error at most ε with probability at least `1−δ` for `0<ε≤1/(1−γ)`, `0<δ<1`, and `N≥c₀ log(S/[δ(1−γ)])/[(1−γ)³ ε²]` for a sufficiently large universal positive constant. The construction here requires N>0 because the empirical frequency 1/N is defined only for a positive sample count; its policy is a fixed input, not chosen from these data.

## What is constructed and proved

`Samples State N` indexes observations by `(s,i)`. `samplingLaw M π N` is the finite product of actual `M.policyTransition π s` row measures, so it directly samples N times per state from the induced transition law as the algorithm specifies, including for randomized stationary policies. The file proves probability normalization, each coordinate's exact marginal, and mutual independence of all coordinates. The true MDP enters the probability law through its transition kernel; it is not supplied as an estimator input through the data.

`empiricalPolicyRow` invokes the existing positive-N `FiniteDistribution.empiricalRow` on each row of data. Its probability vector is the literal empirical frequency and its expectation is the arithmetic sample average. `empiricalModel` embeds the empirical policy transition row and known policy-averaged reward in an MDP by making all action rows identical; its discount is the original known discount. The construction uses `M` as a Lean argument for its known reward, discount, and validity evidence, but its transition field is never read by `empiricalModel` or `valueEstimator`; the unknown transition is used only by `samplingLaw`. The output is the existing uniquely constructed `valueFixedPoint` of this empirical model. `valueEstimator_bellman` proves it satisfies `V̂(s)=rπ(s)+γ P̂π(s) V̂`, and `valueEstimator_unique` proves uniqueness of solutions to this exact equation. This is the intrinsic discounted fixed-point characterization of the source inverse formula. An explicit matrix inverse identity is not yet formalized here. `valueEstimator_measurable` proves data measurability, and `valueEstimator_eq_trajectory` identifies it with actual infinite-path expected value of the empirical model.

## Remaining theorem work

No probability bound, source theorem, universal constant, concentration premise, error estimate, or placeholder is assumed or proved here. To establish the cited theorem, connect the simultaneous empirical-row concentration for fixed true `Vπ` to this product law; prove the exact perturbation/resolvent decomposition and its nonnegative inverse bounds; develop the variance and self-bounding estimates needed for the source's `(1−γ)⁻³` rate across its full ε range; combine events and constants to obtain the displayed `1−δ` guarantee under the source sample threshold; and independently audit the statement, constants' scope, true trajectory target and actual event measurability. If source fidelity requires the literal matrix expression rather than the proved unique Bellman solution, also establish their equality with an invertibility theorem. No source result is certified by these construction lemmas alone.

## Validation

`bash scripts/lean-local.sh .local/ModelBasedPolicyEvaluation.lean` compiled cleanly against project build artifacts. A temporary copy of the exact source with eight appended `#print axioms` commands also compiled cleanly and was deleted. `samplingLaw_probability`, `samplingLaw_marginal`, `samplingLaw_independent`, `empiricalPolicyRow_expectation`, `valueEstimator_bellman`, `valueEstimator_unique`, `valueEstimator_measurable`, and `valueEstimator_eq_trajectory` depend only on `propext`, `Classical.choice`, and `Quot.sound`. Compiler use was coordinated within the two-compiler limit. Integrated export compilation and independent source review remain outstanding.

SHA-256:

- `.local/ModelBasedPolicyEvaluation.lean`: `fe368676ff1a9b30b988112ae3478b3ed46abf1949c66a2169751fb60560aa53`.
- `source/upstream/tex/chapters/generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.
- `Formalization/Probability/EmpiricalRow.lean`: `6e87c90ff1150f7053845acff92d60a5c35035c7a78adcd394e0da5f3d9dc154`.
- `Formalization/MDP/PrefixValueBridge.lean`: `bd286567aa059c3e5fb293f1943eb06bd2e3d79c8dc9484d8a73195a2db16e89`.

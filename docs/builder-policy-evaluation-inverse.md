# Finite-matrix inverse for empirical policy evaluation

`.local/PolicyEvaluationInverse.lean` proves the literal inverse identity for the integrated model-based policy-evaluation estimator. The source algorithm (`generative_model_model_based.tex:78–106`, `eq:value-estimation-MB-inf-vhat`) forms the empirical policy transition matrix and outputs `(I−γ P̂π)⁻¹ rπ`. This staged module derives that formula without assuming invertibility or a performance bound.

`empiricalMatrix` uses the actual probability of each observed empirical row as its matrix entry; `empiricalMatrix_mulVec` identifies matrix-vector multiplication with that row's finite expectation. `policyReward` is the original model's known reward averaged under the fixed policy. `empiricalResolvent_isUnit` proves `I−γ P̂π` invertible: equal outputs on two vectors imply their difference has sup norm at most γ times itself, using the probability-row expectation bound; `0≤γ<1` forces that norm to zero. Finite-dimensional matrix injectivity then yields the unit property. The proof works for all admissible discounts, including zero, and does not assume the matrix is invertible or its inverse is positive.

`valueEstimator_matrix_equation` translates the already established empirical Bellman equation to `(I−γ P̂π) V̂π = rπ`, and `valueEstimator_eq_inverse` applies the proved inverse to get exactly `(I−γ P̂π)⁻¹ rπ = V̂π`. The Lean inverse is Mathlib's ordinary nonsingular matrix inverse, and the separate invertibility theorem prevents its singular-matrix fallback from being used here. The result holds for every positive sample size and every sample value; no concentration hypothesis or error guarantee is assumed.

Validation: `bash scripts/lean-local.sh .local/PolicyEvaluationInverse.lean` compiled cleanly against the integrated `Formalization.Generative.ModelBasedPolicyEvaluation` dependency. An exact temporary source copy with four appended axiom checks compiled and was deleted. `empiricalMatrix_mulVec`, `empiricalResolvent_isUnit`, `valueEstimator_matrix_equation`, and `valueEstimator_eq_inverse` depend only on `propext`, `Classical.choice`, and `Quot.sound`. Compiler use was coordinated within the two-compiler limit. Independent source review, integration and integrated-export audit remain pending; this identity does not prove the policy-evaluation sample-complexity theorem.

SHA-256:

- `.local/PolicyEvaluationInverse.lean`: `d99f9b37bead6b7643377f8fd5572c4c18cf375ff1c6879e6889f0870b91cfc9`.
- `Formalization/Generative/ModelBasedPolicyEvaluation.lean`: `fe368676ff1a9b30b988112ae3478b3ed46abf1949c66a2169751fb60560aa53`.
- `source/upstream/tex/chapters/generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

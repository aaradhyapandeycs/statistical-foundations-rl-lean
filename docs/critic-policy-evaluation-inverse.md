# Independent review: empirical policy-evaluation matrix inverse

Reviewed 2026-11-02. Exact staged file `.local/PolicyEvaluationInverse.lean` SHA-256 `d99f9b37bead6b7643377f8fd5572c4c18cf375ff1c6879e6889f0870b91cfc9`. Reviewer owns only this report. This is ordinary proved infrastructure, not an author-frozen declaration.

## Verdict

**PASS: the exact empirical estimator has the source's literal finite-matrix inverse expression.** No invertibility, approximation, or statistical guarantee is assumed. The formula is established for every positive N and every sample array, using the same model, policy, reward, discount and data as the integrated estimator.

I independently read the raw source at `generative_model_model_based.tex:78–106`, especially `eq:defn-empirical-P-policy-eval` and `eq:value-estimation-MB-inf-vhat`. The algorithm samples N times from each policy-induced transition row, forms the relative-frequency matrix P̂π, and defines V̂π=(I−γP̂π)⁻¹rπ. The staged result proves exactly that formula, with the equality written in the reverse direction. It does not prove the later difference/resolvent perturbation identity or any sample-complexity theorem.

## Matrix, orientation and estimator identity

`empiricalMatrix N hN data s t` is `(empiricalPolicyRow N hN data s).prob t`, literally the relative frequency `(N : ℝ)⁻¹ * ∑ i, if data (s,i)=t then 1 else 0`. Rows are current states and columns are next states. Every row is nonnegative and sums to one by the actual empirical distribution construction; no arbitrary stochastic matrix or row-law certificate is substituted for the observed frequencies.

`empiricalMatrix_mulVec` is definitional equality between matrix-vector multiplication and empirical row expectation. Thus multiplying a column value vector gives the expected next value in the correct direction. The identity matrix is Lean's square matrix `1`, scalar multiplication is entrywise γ, and subtraction forms exactly I−γP̂π. There is no transposition, reversed value orientation, or policy mixture of the empirical rows introduced a second time.

`policyReward M π s` is the finite π-average of the original known reward M.reward at s, namely rπ(s). The integrated empirical model has these state rewards independent of action and the same M.discount. Its repeated action rows are the same empirical policy row. Consequently the Bellman equation used by the new module is exactly V̂π=rπ+γP̂πV̂π, including for a randomized stationary π.

The inverse theorem uses the unchanged `valueEstimator M π N hN data`, not a new inverse-defined estimate. Its `empiricalMatrix` and reward vector receive exactly the same parameters/data. The estimator already has proved uniqueness and `valueEstimator_eq_trajectory`, identifying it with the actual infinite discounted reward expectation under the empirical model's controlled trajectory law. This module's algebra therefore concerns the same actual plug-in trajectory value, not an unexplained nominal fixed point.

The actual sample law in the imported module is the finite product of the true policy-transition-row measures, with proved coordinate marginals and joint independence. The inverse equation is pointwise in data and needs none of those probability facts as assumptions. It remains valid for every array in that experiment.

For `empiricalMatrix` and `policyReward`: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS.

## Invertibility and nonsingular inverse

I checked the invoked APIs in the pinned Mathlib `Matrix/NonsingularInverse.lean`. `Matrix.mulVec_injective_iff_isUnit` genuinely turns injectivity of multiplication by a finite square matrix over ℝ into the matrix's unit property. `Matrix.inv_mulVec_eq_vec` uses an `Invertible` instance to cancel the ordinary nonsingular matrix inverse.

The staged proof supplies injectivity rather than assuming it. If (I−γP̂π)x=(I−γP̂π)y, rowwise rearrangement gives x−y=γP̂π(x−y). Nonnegative normalized empirical rows bound each expected difference in absolute value by ‖x−y‖∞, so ‖x−y‖∞≤γ‖x−y‖∞. The actual MDP conditions 0≤γ<1 force zero norm and hence x=y. The finite-dimensional injectivity result then proves `IsUnit (I−γP̂π)`.

The final theorem creates `Invertible` solely from this proved unit property and applies the pinned cancellation theorem to the proved matrix equation. Mathlib's matrix inverse has total off-invertible semantics, but that fallback is unreachable here: nonsingularity has already been proved for every declared input. No determinant nonzero premise or inverse positivity premise is hidden in a local instance.

The proof is valid at γ=0. Its contraction argument and final inverse use no division by γ; then the matrix is I and the value is rπ. Positive N is explicit and matches relative-frequency construction; no N=0 empirical row is invented.

## Expanded binder inventory

These are all input families across the four theorem exports; a binder used repeatedly has the same classification throughout.

| Expanded input | Bin | Basis |
|---|---|---|
| State | TYPING | Finite source state carrier |
| Action | TYPING | Finite source action carrier |
| Fintype State | STANDING | Finite MDP |
| Fintype Action | STANDING | Finite MDP |
| DecidableEq State | TYPING | Locally constructed from classical equality, not an additional supplied premise |
| M.state_nonempty | STANDING | Nonempty source state set |
| M.action_nonempty | STANDING | Nonempty source action set |
| M.transition | STANDING | True stationary transition rows |
| Each transition mass nonnegative | STANDING | Probability distribution definition |
| Each transition row sum =1 | STANDING | Probability distribution definition |
| M.reward | STANDING | Known reward input |
| M.reward_nonneg | STANDING | Source [0,1] reward convention |
| M.reward_le_one | STANDING | Source [0,1] reward convention |
| M.discount | STANDING | Known discount input |
| M.discount_nonneg | STANDING | Source 0≤γ |
| M.discount_lt_one | STANDING | Source γ<1 |
| π | SOURCE | Evaluated stationary policy |
| Each π-row nonnegative | TYPING | Probability policy definition |
| Each π-row sum =1 | TYPING | Probability policy definition |
| N | SOURCE | Sample count |
| hN : 0<N | SOURCE | Positive count in source relative frequencies |
| data | TYPING | Observed source sample array |
| V (only multiplication lemma) | TYPING | Arbitrary value test vector |
| s (only multiplication lemma) | TYPING | State query |

Inventory counts: SOURCE 3, STANDING 13, TYPING 8, RULED 0, EXCESS 0. Neither invertibility nor a desired error estimate appears among the premises. The local inverse instance is a produced proof, not an assumed binder. M.transition does not enter the empirical matrix or the inverse computation; it determines the experiment in the imported sampling law.

## Limits and identity

This result closes the inverse representation obligation for the integrated empirical value estimator. A source error bound, a norm bound on the inverse, the true/empirical difference-resolvent identity, concentration and the policy-evaluation statistical theorem still require their own proofs. Proved empirical inverse construction alone must not be counted as those claims.

Imported `Formalization/Generative/ModelBasedPolicyEvaluation.lean` hash was independently recomputed as `fe368676ff1a9b30b988112ae3478b3ed46abf1949c66a2169751fb60560aa53`; source chapter hash is `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

## Independent compilation and axioms

After coordinating a compiler slot with the lead and other workers, I copied the exact reviewed source unchanged to `.local/InverseIndependentAudit.lean`, appended four `#print axioms` commands, and ran:

`bash scripts/lean-local.sh .local/InverseIndependentAudit.lean`

Exit status 0, without warnings or errors. `empiricalMatrix_mulVec`, `empiricalResolvent_isUnit`, `valueEstimator_matrix_equation`, and `valueEstimator_eq_inverse` each report exactly the allowed axioms `propext`, `Classical.choice`, `Quot.sound`. The temporary source was deleted. No `sorry`, `admit` or custom axiom is declared in the reviewed source. This is exact staged-source and transitive axiom evidence; production integration and the integrated export audit remain lead responsibilities.

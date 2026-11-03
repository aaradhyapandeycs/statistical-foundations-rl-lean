# Staged model-based policy-learning construction

`.local/ModelBasedPolicyLearning.lean` implements the Chapter 3 generative-model policy-learning algorithm through its empirical model and an empirically optimal deterministic policy. It does **not** assume or prove the source sample-complexity theorem. This is staged proof evidence pending independent review and integration.

## Source and experiment

The source (`generative_model_model_based.tex:814–865`, `alg:policy-learn-model-based`) draws N independent next states for every state-action pair, defines each empirical transition row by relative frequencies, keeps the known reward and discount, and returns a deterministic optimal policy of the empirical MDP. It permits any optimal deterministic choice; no particular tie rule is prescribed. The accompanying theorem `Thm:sample-compl-main` (`:898–922`) asserts simultaneous true-model inequalities `V^π̂≥V*−ε` and `Q^π̂≥Q*−γε` with probability at least `1−δ`, for `0<ε≤1/(1−γ)` and `0<δ<1`, when `N≥c₀ log(SAN/[(1−γ)²εδ])/[(1−γ)³ε²]` for a universal positive constant. N is implicitly present inside the logarithm; this staged construction assumes N>0 so empirical frequencies exist.

`Samples State Action N` indexes one state observation by `((s,a),i)`. `samplingLaw` is the finite product of the true state-action transition measures, not an arbitrary law. Its probability normalization, exact coordinate marginal, and mutual independence across all state-action/sample coordinates are proved. `empiricalRow` is the existing empirical frequency distribution for the corresponding observations, and its expectation is proved equal to their sample mean. `empiricalModel` uses exactly those rows, with original known reward and discount. Although the ambient MDP is a Lean argument, the empirical-model body does not read its true transition; that kernel only determines the sampling law.

`qEstimator` is the empirical optimality fixed point. `qEstimator_bellman` and `qEstimator_unique` prove that it is the unique solution of the empirical optimality equation. `policyEstimator` chooses the existing empirical optimal greedy action; its use of classical choice gives a deterministic selection, with a maximizing choice at ties. `valueEstimator` is the actual infinite-trajectory value of that policy in the empirical MDP. `qEstimator_eq_trajectory` proves that the Q estimator is its actual empirical forced-first-action trajectory Q for every state and action, and `policyEstimator_empirical_optimal` proves its empirical trajectory value simultaneously dominates every stationary randomized policy. All three output functions are measurable in sample data: the sample space is finite with discrete measurable structure. This proves measurability for each fixed known model input; joint measurability in varying reward and discount is not established.

## Remaining theorem work

Empirical optimality is not true-model near-optimality. In particular, the empirical policy depends on the same samples, so fixed-policy concentration cannot be applied to it as though it were independent. A complete source theorem requires suitable uniform or decoupled concentration, the relevant empirical and true trajectory Bellman/resolvent perturbation identities, variance and self-bounding estimates over the source's full ε range, control of the data-dependent policy, a probability bound on the simultaneous V and Q events, and the source's universal constant and exact N-dependent logarithm. It also needs independent statement/source review and integrated axiom checks. No error event or bound is assumed here, and this construction does not certify the theorem or all choices of empirical optimizer.

## Validation

`bash scripts/lean-local.sh .local/ModelBasedPolicyLearning.lean` compiled cleanly. A temporary copy of the exact source with eleven appended `#print axioms` commands was compiled and deleted. The inspected probability, marginal, independence, empirical expectation, three measurability, Q Bellman and uniqueness, Q trajectory, and empirical optimality declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. Compiler use was coordinated within the two-compiler limit. The initial check had an unused section-variable lint warning; after excluding that irrelevant instance, the final check was clean.

SHA-256:

- `.local/ModelBasedPolicyLearning.lean`: `6f568330fd0744f11c0e965e5e3fd884dac5fd579965bbe4d7918f571e8c4f8c`.
- `source/upstream/tex/chapters/generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.
- `Formalization/Probability/EmpiricalRow.lean`: `6e87c90ff1150f7053845acff92d60a5c35035c7a78adcd394e0da5f3d9dc154`.
- `Formalization/MDP/OptimalTrajectoryValue.lean`: `d3fbac88b1bec5e29ad93e9432d6a491f72fb3d9ada243f3a954950b47af21d7`.

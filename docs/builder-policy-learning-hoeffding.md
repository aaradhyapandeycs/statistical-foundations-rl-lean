# Conservative policy-learning guarantee

`.local/PolicyLearningHoeffding.lean` proves an actual-law finite-sample guarantee for the empirical MDP's greedy policy at every discount in `[0, 1)`. For `0 < δ < 1` and `N > 0`, with probability greater than `1 - δ`, the true trajectory-value loss at every state is at most

`2 γ / (1 - γ)^2 * sqrt(log(2 K / δ) / (2 N))`,

where `K = |Action^State × State × Action|`. The sampling law is the genuine product of transition-row laws. The proof applies fixed-vector Hoeffding simultaneously to each state-action row and the true trajectory values of all deterministic policies. It then selects the empirical greedy policy inside that simultaneous event; it never assumes this data-dependent policy is independent of its training samples. Empirical trajectory optimality and policy-value perturbation yield the loss bound.

This is a conservative rate, not the sharp source theorem: the union over deterministic policies enlarges the logarithm, and the horizon factor is worse. No sample-complexity corollary or source-sharp guarantee is claimed. The result remains a scratch declaration rather than an integrated export, pending independent review.

Validation: `lake env lean .local/PolicyLearningHoeffding.lean` passed. A separate temporary `#print axioms` probe reported only `propext`, `Classical.choice`, and `Quot.sound` for `policyEstimator_hoeffding`. No independent source or semantic audit has yet been completed.

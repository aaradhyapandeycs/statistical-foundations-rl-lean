# Independent review: policy learning at zero discount

Reviewed 2026-11-02. Exact staged target `.local/PolicyLearningZeroDiscount.lean` SHA-256 `b75ba66b5c4d4c2be3cb8b2978f1ea9b74afa4f10b4b078b7d51a209f7c6be3e`. This reviewer owns only this report. The imported policy-learning construction has SHA-256 `6f568330fd0744f11c0e965e5e3fd884dac5fd579965bbe4d7918f571e8c4f8c`, matching the previously independently reviewed construction.

## Semantic verdict

**PASS within its explicit γ=0 scope.** The result is exact, pointwise for every positive sample count and every observation array, and yields a probability-one joint true-model success event. It does not establish the source theorem for positive discount or all choices of empirical optimizer.

I checked the source standing discount range `prelim.tex:31–45`, its actual trajectory Q/V definitions `:90–123`, the empirical policy-learning algorithm `generative_model_model_based.tex:814–865`, and the separate general guarantee `:898–922`. Zero discount belongs to the source range [0,1). This is a legitimate explicitly restricted boundary case; it must not be promoted as the full theorem.

The two central equalities use **M**, the true model, outside the trajectory expectation. Only the chosen policy is built from the empirical model. Both right-hand sides are actual true trajectory values of the true optimal greedy policy. Thus these are true-model performance claims, not empirical-model optimality relabeled as a guarantee.

At γ=0, every policy's forced-first-action actual Q is M.reward(s,a). The proof reaches that equality through the established trajectory/Q-Bellman bridge and the policy fixed-point equation. The designated first action contributes immediate reward even if its policy probability is zero. This alone explains equality of Q for every policy at the endpoint; it would not establish V optimality for an arbitrary policy.

The separate V proof correctly supplies the needed extra fact: the empirical model preserves M.reward and M.discount, so its Q fixed point equals the same reward table at γ=0. Its chosen greedy action therefore maximizes **true** immediate reward at every state. Averaging actual Q under the point-mass action law gives precisely that maximal reward, equal to the true optimal greedy policy's V. Tie choice has no effect on this value equality, but the theorem itself names only the implemented selector.

No assertion that the empirical transition is accurate is used. No sample event, high-probability premise, concentration lemma or loss estimate is assumed. All sample arrays are allowed, including outcomes of zero probability under the true kernel. The condition N>0 is inherited from the algorithm's frequency rows; no zero-sample extension is invented.

The full-array norm statement follows from the proved simultaneous pointwise equalities. The probability theorem then proves its joint event is Set.univ and uses normalization of the actual `samplingLaw M N`, the finite product of the true state-action transition rows. It does not use an arbitrary favorable probability law, a conditional event or a measure-zero argument.

## Expanded input inventory

| Input | Bin | Basis |
|---|---|---|
| State | TYPING | State carrier |
| Action | TYPING | Action carrier |
| Fintype State | STANDING | Finite source MDP |
| Fintype Action | STANDING | Finite source MDP |
| M.state_nonempty | STANDING | Nonempty source state space |
| M.action_nonempty | STANDING | Nonempty source action space |
| M.transition | STANDING | True stationary transition rows |
| Transition masses nonnegative | STANDING | Probability row definition |
| Transition rows sum =1 | STANDING | Probability row definition |
| M.reward | STANDING | Known immediate reward |
| M.reward_nonneg | STANDING | Source [0,1] reward convention |
| M.reward_le_one | STANDING | Source [0,1] reward convention |
| M.discount | STANDING | Known source discount |
| M.discount_nonneg | STANDING | Source 0≤γ |
| M.discount_lt_one | STANDING | Source γ<1 |
| hγ : M.discount=0 | SOURCE | Explicit endpoint specialization, not a premise of the general source theorem |
| π (only general Q helper) | TYPING | Arbitrary stationary randomized policy |
| π-row nonnegative | TYPING | Probability policy definition |
| π-row sum =1 | TYPING | Probability policy definition |
| N | SOURCE | Algorithm sample count |
| hN : 0<N | SOURCE | Positive frequency denominator |
| data | TYPING | Arbitrary full sample outcome |
| s | TYPING | State query |
| a | TYPING | Forced first-action query |

Inventory counts: SOURCE 3, STANDING 13, TYPING 8, RULED 0, EXCESS 0 for these explicitly scoped endpoint claims. Relative to an attempt to certify the **general** source theorem, hγ would instead be an EXCESS restriction and certification would fail. This report makes no such promotion.

The selected policy is the actual imported empirical greedy selector. The proof does not replace it with the true greedy selector, assume their action functions coincide, or assume the desired optimality. It proves equality of their values by their common reward-maximality. The true comparison policy's established optimizer semantics are within the manuscript's stationary randomized-policy convention.

## Remaining scope and verification

The general positive-discount statistical theorem, its universal constant, N-dependent logarithm, full precision range, and statement for any empirical optimal selector remain separate obligations. This endpoint result does not imply any of them. Production integration and integrated-export checks remain the lead's responsibility.

After coordinating compiler slots, I copied the exact reviewed source unchanged to `.local/ZeroDiscountIndependentAudit.lean`, appended seven `#print axioms` commands and ran:

`bash scripts/lean-local.sh .local/ZeroDiscountIndependentAudit.lean`

Exit status 0 without warnings or errors. `trajectoryQ_zero_discount`, `optimalQ_zero_discount`, `greedy_reward_zero_discount`, `policyEstimator_trueQ_zero_discount`, `policyEstimator_trueValue_zero_discount`, `policyEstimator_loss_zero_discount`, and `policyEstimator_success_zero_discount` each report only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom declaration occurs in the source. The temporary source was deleted. This verifies the actual staged file and its transitive axiom closure, not a future integration diff.

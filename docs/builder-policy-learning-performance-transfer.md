# Deterministic optimal-policy performance transfer

Stable staged source: `.local/PolicyLearningPerformanceTransfer.lean`.
SHA-256: `a0bd5f59289707d9a4a0739914e960c76a4b04335b14acfdfc1f55806ccb825d`.

This file imports only the production `Formalization.Generative.PolicyLearningHoeffding` module. It completes a deterministic connection, not the probabilistic policy-learning theorem.

## Source correspondence

The pinned `source/upstream/tex/chapters/generative_model_model_based.tex`, lines 976–985, proves that uniform value loss at most ε gives Q loss at most γε using the true transition row. Lines 1016–1029 decompose the fitted-policy value loss into true-optimal and fitted-policy evaluation errors, dropping the empirical-optimality term. The implementation consumes the existing proved `policyEstimator_loss_le_evaluation_errors`, which discharges this empirical optimality using the actual empirical greedy policy. It does not assume the desired performance bound or empirical optimality anew.

## Five exports

In `StatisticalRL.DiscountedMDP`:

1. `trajectoryQ_eq_reward_add_trajectoryValue` identifies actual forced-first-action Q with reward plus discounted expectation of the same policy's actual continuation value. The underlying forced-prefix bridge covers actions outside policy support.
2. `trajectoryQ_sub_eq_discount_expectation_value_sub` gives the exact two-policy difference identity, with factor γ and the true transition distribution.
3. `trajectoryQ_loss_le_discount_of_value_loss` derives nonnegative optimal Q loss and upper bound γε from a uniform actual V loss bound.
4. `trajectoryQ_loss_norm_le_discount_of_value_loss` proves both finite supremum-norm bounds; the nested function norm for Q is the maximum over state and action.

In `StatisticalRL.ModelBasedPolicyLearning`:

5. `policyEstimator_performance_of_evaluation_errors` consumes the two actual empirical-versus-true evaluation norm budgets ε₀ and ε₁ and concludes, simultaneously at every state/action, `0 ≤ V*−Vπhat ≤ ε₀+ε₁` and `0 ≤ Q*−Qπhat ≤ γ(ε₀+ε₁)`. The empirical model, estimator and all evaluation functions use exactly the same sample data. No independence is used or claimed for the fitted policy. Equal half-budgets give source ε and γε with no extra factor.

Both carriers are arbitrary finite types; the MDP supplies nonemptiness, rewards in [0,1], stochastic transitions, and 0≤γ<1. The generic V-to-Q lemma allows stationary randomized policies; the actual fitted-policy corollary uses the established deterministic selector. Every statement includes γ=0 without division by γ; Q loss is then exactly zero. N>0 is required solely by the empirical model construction. Every sample outcome is covered, without a probability event premise beyond the explicitly supplied evaluation budgets.

## Validation

`bash scripts/lean-local.sh .local/PolicyLearningPerformanceTransfer.lean` exited 0 with no diagnostics. An exact-source-copy probe `.local/PolicyLearningPerformanceTransferAudit.lean` appended `#print axioms` for all five exports; its compile exited 0 and every export reported only `propext`, `Classical.choice`, and `Quot.sound`. No custom axioms or admissions occur. These are staged source checks against existing production dependencies; production integration and independent review remain separate requirements.

## Remaining work

The two evaluation budgets must still be established together with the intended confidence and source sample complexity. In particular, this deterministic result makes no probability assertion and does not permit applying a fixed-policy probability theorem directly to a fitted policy. It also makes no claim about arbitrary tie-breaking algorithms beyond the implemented empirical greedy selector. Source-shaped reversed inequalities follow algebraically from the displayed nonnegative losses.

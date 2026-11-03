# One-state Bellman obstruction: builder report

`Formalization/Obstructions/OneState.lean` proves the exact one-state formula against the existing `DiscountedMDP` Bellman operators, for every finite `State` with `[Subsingleton State]` and every finite `Action`. The MDP supplies nonemptiness of both carriers, a genuine finite probability distribution for each transition, reward bounds, and `0 ≤ discount < 1`. The construction selects the finite maximum over actions using the MDP's nonempty-action field.

For each state and initial action, `oneStateQ` is

```text
reward(s,a) + discount * max_b reward(s,b)/(1−discount).
```

It is computed using only reward and discount: `oneStateQ_eq_of_reward_discount_eq` proves equal outputs for any two admissible models with equal rewards and discount, independently of their transition kernels. `oneStateQ_qOptimality` proves the formula is a fixed point of the actual `qOptimality` operator. `optimalityFixedPoint_eq_oneStateQ` then identifies it with the existing unique optimality fixed point. A reward-maximizing action is obtained by finite maximization, and `oneStateGreedyPolicy` represents the resulting stationary deterministic policy by point masses. `greedy_policyFixedPoint_eq_optimalityFixedPoint` proves its existing policy Bellman fixed point equals the optimality Bellman fixed point, including all initial actions.

The proof uses singleton-state equality to turn each transition expectation into the expectation of a constant. It proves the relevant Bellman equations directly; no value or desired result is supplied as a hypothesis. Finite maximization is actual `actionMaximum`, not an assumed maximizer. The counterexample's numerical parameter feasibility is documented separately in `docs/critic-one-state-review.md`.

## Validation

- `bash scripts/lean-local.sh Formalization/Obstructions/OneState.lean`: passed with no diagnostics.
- `bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/Obstructions/OneState.olean Formalization/Obstructions/OneState.lean`: passed with no diagnostics. This produced a project-owned build artifact, without rebuilding dependencies.
- An ephemeral external probe imported the compiled module and ran `#print axioms` on `oneStateQ_eq_of_reward_discount_eq`, `oneStateQ_qOptimality`, `optimalityFixedPoint_eq_oneStateQ`, and `greedy_policyFixedPoint_eq_optimalityFixedPoint`. Each reported exactly `propext`, `Classical.choice`, and `Quot.sound`. The probe was removed afterward.
- Source file SHA-256 at validation: `87db477c4dbcb5badbdbbdbbe438cfea4ff3a64b513ea332da33a62b325f072e`.

## Scope and review

This is Bellman fixed-point evidence only. Identification with source-defined infinite-trajectory optimal Q, the statistical experiment, and the failure-event probability requires separate bridges and review; the results here do not by themselves certify or refute the full source theorem in Lean. Independent review and affected integration checks are pending. No proposed corrected theorem or source amendment is adopted.

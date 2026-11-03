# Independent review of the one-state Lean obstruction

**Verdict: PASS for the stated Bellman fixed-point formula and the greedy
policy's Bellman fixed point. This is not a Lean proof of the paper's
trajectory-value or minimax counterexample.**

## Source-first reconstruction

The authoritative model-based chapter, lines 11–31, supplies independent
transition samples and known rewards; `prelim.tex` lines 31–45 supplies finite
state/action sets, stochastic transitions, deterministic rewards in `[0,1]`
and `0 ≤ γ < 1`. The source's `Q^π` is the infinite expected discounted
trajectory return (prelim lines 114–123), and `Q*` is induced by an optimal
policy (lines 136–140). The minimax theorem at model-based lines 1443–1463
quantifies over every estimator and claims an adversarial MDP for fixed sizes
`SA ≥ 16`. In particular its displayed hypotheses do not exclude `S = 1`.

For one nonempty state the transition necessarily returns that same state.
For arbitrary bounded reward tables and `γ < 1`, the anticipated result is
`Q*(s,a) = r(s,a) + γ max_b r(s,b)/(1−γ)`. A reward-maximizing action then
attains the fixed point. The statistical obstruction additionally needs one
uniform estimator based only on available known inputs, its measurable output
on the sample space, equality to source trajectory `Q*`, and a concrete
admissible selection of the theorem's parameters and probability event. That
entire inference is not equivalent to merely proving a Bellman identity.

## Examination of the implementation

- `oneStateQ` (OneState.lean lines 29–32) is exactly the stated algebraic
  formula, with a genuine finite maximum and a positive denominator under
  `discount_lt_one`. `oneStateQ_eq_of_reward_discount_eq` (34–39) proves that
  changing the model while preserving the reward table and discount cannot
  change the formula. While the definition accepts a whole MDP as input, the
  proved equality supports dependence on those two fields only; in the source
  problem they are known or fixed.
- `DiscountedMDP` carries finite state/action types, nonempty state and action
  witnesses, actual nonnegative normalized transition vectors, rewards in
  `[0,1]`, and `0 ≤ γ < 1`. Adding `[Subsingleton State]` to the result therefore
  means exactly one state. It does not assume the sought formula, optimality,
  or any favorable transition property. The stronger discount interval in the
  minimax theorem is not needed for this identity.
- `oneStateQ_qOptimality` (41–60) proves the formula is a fixed point of the
  project's actual `qOptimality` operator. It uses equality of every successor
  state to the current state, normalization of each transition expectation,
  finite-max translation by a constant, and `γ < 1`. `FixedPoint.lean` lines
  51–59, 73–80 and 93–99 supplies existence, uniqueness and the defining
  equation of the selected fixed point, so `optimalityFixedPoint_eq_oneStateQ`
  (OneState lines 62–66) is an actual equality, not a fixed-point assumption.
- `oneStateGreedyAction_reward` (68–78) selects an attained maximum of the
  reward table; `oneStateGreedyPolicy` (80–83) encodes the action by a point
  mass. `greedy_policyFixedPoint_eq_optimalityFixedPoint` (85–109) proves its
  policy Bellman Q fixed point equals the optimality Bellman fixed point for
  every action. The choice is classical, consistent with the recorded axiom
  closure; executable tie-breaking or measurability is not established here.
- No unexpected mathematical hypotheses occur in these statements. Their
  conclusions speak about Bellman fixed points. Neither the code nor this
  review identifies these fixed points with the source's infinite trajectory
  returns, constructs a sample space or estimator measurable on it, proves
  `SA ≥ 16` and the sample/epsilon inequalities for a concrete admissible
  instance, or formalizes failure of the quantified minimax assertion. The
  independent mathematical argument in `docs/critic-one-state-review.md`
  remains a source-level counterexample, not a Lean-certified refutation.

## Validation and identity

A temporary copy with `#print axioms` was checked using
`bash scripts/lean-local.sh <temporary-probe>`; it compiled.
For `oneStateQ_eq_of_reward_discount_eq`, `oneStateQ_qOptimality`,
`optimalityFixedPoint_eq_oneStateQ`, `oneStateGreedyAction_reward`, and
`greedy_policyFixedPoint_eq_optimalityFixedPoint`, Lean reported only
`propext`, `Classical.choice`, and `Quot.sound`. The temporary file was removed.
No integration build or exact statistical counterexample probe was performed.

SHA-256 digests:

- `Formalization/Obstructions/OneState.lean`: `87db477c4dbcb5badbdbbdbbe438cfea4ff3a64b513ea332da33a62b325f072e`
- `Formalization/MDP/FixedPoint.lean`: `b7c7b6338d1ec5005942e3b0f80676ed8e0e2dfb650a2cb01638642fe65f642e`
- `Formalization/MDP/Basic.lean`: `ecf28ee04a78405be352f5453d957f34a7883d33304b21255a9f7f444e0bc088`
- `Formalization/MDP/FiniteOptimal.lean`: `abd23ed8206032df152160f50d838d91bf99a169a09bbf2612bc5e9608494e85`
- `source/upstream/tex/chapters/prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`
- `source/upstream/tex/chapters/generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`

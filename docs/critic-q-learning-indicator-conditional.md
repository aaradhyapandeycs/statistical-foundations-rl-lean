# Independent review: Q-learning fresh-indicator conditional expectation and pullout

Reviewed the builder's final exact sources:

- `QLearningIndicatorCondExpDraft.lean` (private staged draft, not shipped), SHA-256 `37defd8793aee4b50fcee3e16c576659411a98a51b7601506d041c1ef813936d`.
- `QLearningConditionalPulloutDraft.lean` (private staged draft, not shipped), SHA-256 `38362fac2b5eceea7d38dac6bb90b9b2f70b54d8001ceb69e0cc7d2d70efa939`.

The exact staged dependency chain rebuilt in this audit was: Q iterate `594b96eede407a268bad69041146728a7456478c39c53990c53bef006a5b207e`; Q sampling `70dccffe5af0e7f824226c1d235257f4b0ea8e4ff7a5f9aaf8d9d1e06a830937`; causality `3eade75e34d1dc7c5a2f6e809e0fe2f8e7fe197ca2b288761df2078067276d37`; conditional-moment definitions `ac450a4871fedcd8320e36c00d1379c2beaa385369b5fab08e709bbf4596176a`; prefix filtration `266f86ca30a206f0bb471742970ca49013f04cf6326a29fd7d6ac0e02f26d30c`; indicator decomposition `60daddba566a81f0d6ae72421153b0104bbde30e7efed60f0d0f1bc59dccdfc7`; and scalar indicator sigma/strong measurability `2dc13db7db500f5128a9207e41dd98288a6df14c009d1799103726ad3ef03c76`. The actual probability layer is production `Formalization.Probability.EmpiricalRow`.

## Source/semantic review

PASS for the stated indicator facts and general finite predictable-sum conditional expectation. `qFreshIndicator` is exactly the indicator that the actual fresh coordinate at layer `t` equals state `x`. Its generated sigma algebra is independent of the strict-prefix sigma algebra under the actual product law; the fresh-row marginal is the actual `M.transition s a` distribution.

The integral identity maps the full data law through that coordinate, rewrites by the actual marginal theorem, then uses the row-measure integral formula for the point indicator. This yields `(M.transition s a).prob x` for every atom, including zero-probability atoms. No division, support positivity, or positive-mass hypothesis occurs. The conditional indicator identity is the independence conditional-expectation theorem followed by this actual integral calculation. `qSampling_integrable` is valid for arbitrary real statistics because the complete finite sample domain is finite; it is not an assumption about the target conditional moments.

For predictable coefficients `c x`, the pullout theorem assumes only strong measurability with respect to the strict past. On the finite experiment, each coefficient, indicator, and product is integrable. Conditional expectation distributes over the finite state sum and pulls out each coefficient, giving the exact weighted sum of actual transition probabilities. It does not assume conditional centering or a variance formula.

## Fresh exact-source compile and axiom audit

The hash-pinned private audit script `audit-q-learning-conditional-indicators-independent.sh` (not shipped) rebuilt all nine modules in dependency order under an isolated local audit directory (not shipped). All compiled successfully. The three new final declarations and their exact staged dependency exports were included in a 51-declaration `#print axioms` probe; every declaration used only `propext`, `Classical.choice`, and `Quot.sound` (or a subset). Compiler output contained only the handoff's noted unused-instance/unused-simp-argument linter warnings.

## Limits

The indicator bridge does not yet instantiate its coefficient pullout with the Q-learning value and squared centered value to prove conditional centering/variance of `qRowIncrement`. The exact variance identity, increment martingale statement, filtration monotonicity/ambient-domain details, Freedman application, and rate theorem remain outstanding. The Lean source headers still label repaired files “Uncompiled”; this stale comment does not change the compiled declarations. Production import integration and export auditing remain separate.

Production integration: reviewed source declarations and proofs compile under production module names; staged imports and stale staging-only comments were updated. The complete project export compiled and audited 2,863 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.

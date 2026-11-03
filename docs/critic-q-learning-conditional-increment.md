# Independent review: Q-learning conditional centering and true-row variance

Reviewed `.local/QLearningConditionalIncrementDraft.lean`, SHA-256 `37819b3b3e5114e277de9a124f2f5bdddffe0dfd679b92aa3948de30fb5483ab`, against the final handoff `docs/builder-q-learning-conditional-increment.md` and exact audited indicator/prefix dependencies in `docs/critic-q-learning-indicator-conditional.md` and `docs/critic-q-learning-prefix-filtration.md`.

## Source/semantic review

PASS for both conditional identities. `qValueBefore` is the actual synchronous Q-learning value after t updates, and the prefix factorization makes it measurable with respect to the strict history `qPastSigma T t`. The row mean `qRowMean` is the expectation under the actual transition `M.transition s a`, and its strong measurability follows as a finite sum of prefix-measurable values with deterministic probability coefficients.

For `t<T`, the current coordinate is present and independent of the complete strict past under the actual product sampling law. The indicator bridge gives its conditional mean as the actual row probability, with zero-probability atoms included. Expanding the sampled value as a finite sum over fresh-state indicators and applying the predictable-sum pullout yields the conditional mean of the sampled value as `qRowMean`. Subtracting this prefix-measurable mean gives `qRowIncrement_condExp_zero`.

For the square identity, the centered increment is expanded pathwise as a finite one-hot sum with coefficient `(V_t(x)−rowMean(V_t))²`. Each coefficient is prefix-strongly measurable; the finite-sum theorem pulls it through conditional expectation. The actual indicator probabilities then yield exactly `qRowVariance M s a V_t`, the variance of the predictable Q-learning value under the true transition row. The only time premise is `t<T`; there is no assumed conditional-moment identity, support positivity, step-size constraint, or boundedness premise. Integrability is justified by the finite complete experiment. When `T=0`, no `t<T` exists, so these current-draw statements are vacuous.

## Fresh exact-source compilation and axiom audit

Verified the final staged hash and rebuilt the exact 10-module chain in `.local/q-learning-conditional-increment-independent-audit`: Q iterate, sampling law, causality, conditional-moment definitions, prefix filtration, pathwise indicator expansions, indicator sigma algebra, conditional indicator bridge, predictable-sum pullout, and the final increment specialization. Compilation completed successfully; only unused-instance/simp-argument linter warnings appeared. The import audit probed 55 declarations; every export used only `propext`, `Classical.choice`, and `Quot.sound` (or a subset).

## Remaining scope

These are conditional identities given the entire strict sample prefix. They do not by themselves provide a filtration API with monotonicity/ambient inclusion, transfer to the smaller prior-increment history, an MDS theorem, Freedman inputs, concentration or a learning-rate theorem. Production integration/export checks also remain separate. The Lean module comment still says “Source-only draft”; that comment is stale relative to the compiled source and handoff.

Production integration: reviewed source declarations and proofs compile under production module names; staged imports and stale staging-only comments were updated. The complete project export compiled and audited 2,863 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.

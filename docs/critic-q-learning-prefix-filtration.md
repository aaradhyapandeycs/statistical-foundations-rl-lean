# Independent review: Q-learning whole-layer prefix filtration

Current reviewed source `QLearningPrefixFiltrationDraft.lean` (private staged draft, not shipped), SHA-256 `266f86ca30a206f0bb471742970ca49013f04cf6326a29fd7d6ac0e02f26d30c`, matches the builder handoff `docs/builder-q-learning-prefix-filtration.md`. This is a new exact-source review after the earlier predecessor hash `4a5b39c9d54a356d31528d94e71b6444b4c0b7cc5e8da8ccdb76046b2b534626`; the current source's `qValue_stronglyMeasurable_past` proof now explicitly factors through the finite prefix code rather than relying on an unverified measurable-maximum tactic.

The dependencies independently rebuilt here were `QLearningConditionalMomentsDraft.lean` (private staged draft, not shipped) (SHA `ac450a4871fedcd8320e36c00d1379c2beaa385369b5fab08e709bbf4596176a`), `QLearningCausalityDraft.lean` (private staged draft, not shipped) (SHA `3eade75e34d1dc7c5a2f6e809e0fe2f8e7fe197ca2b288761df2078067276d37`), `QLearningSynchronousSampling.lean` (private staged draft, not shipped) (SHA `70dccffe5af0e7f824226c1d235257f4b0ea8e4ff7a5f9aaf8d9d1e06a830937`), and `QLearningIterateBounds.lean` (private staged draft, not shipped) (SHA `594b96eede407a268bad69041146728a7456478c39c53990c53bef006a5b207e`). The source algorithm is in `source/upstream/tex/chapters/generative_model_model_free.tex:794–870`.

## Source/semantic review

PASS for the stated full-layer independence and finite-prefix measurability. The strict past contains exactly product coordinates with time `<t`; the current layer contains exactly coordinates with time `=t`. They are disjoint for every t. For `t<T` this layer has one coordinate for each state/action row; for `t≥T` it is empty. Thus `T=0` has empty past and layer and no fabricated sample at time zero.

The actual full product law establishes independence of the past and current-layer code maps, and the `comap` definitions give their generated sigma algebras. The theorem places the current-layer sigma algebra first and the past sigma algebra second, which is the needed orientation for conditioning on the past. `qIterate_measurable_past` composes the finite-code Q iterate with `qPastData`, using the exact pathwise prefix-factorization result; the current revised value-coordinate proof does the same for the finite action maximum. These are measurable finite-domain constructions. The marginal theorem separately identifies each current coordinate with its actual transition-row law.

## Fresh exact-source compilation and axiom audit

Verified the five exact hashes above and ran the private audit script `audit-q-learning-prefix-filtration-independent.sh` (not shipped), rebuilding iterate, sampling, causality, conditional-moment definitions, and current prefix source in dependency order under an isolated local audit directory (not shipped). All compiled successfully without diagnostics. `#print axioms` covered 38 declarations; every export uses only `propext`, `Classical.choice`, and `Quot.sound` (or a subset).

## Remaining scope

The conditional-moment dependency contains definitions only; no conditional-expectation identity is assumed or proved by this module. Sigma-algebra monotonicity/ambient domination, integrability, rowwise conditional centering and variance, martingale properties, Freedman inputs, and concentration/rate results remain outstanding. The Lean header still calls this a “source draft” despite the successful staged compilation; this is a stale comment only. Production integration and production import/export audits are separate.

Production integration: reviewed source declarations and proofs compile under production module names; staged imports and stale staging-only comments were updated. The complete project export compiled and audited 2,863 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.

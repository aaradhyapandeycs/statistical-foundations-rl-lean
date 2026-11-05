# Independent review: Q-learning increment and row-variance caps

## Exact source and validation

Reviewed `QLearningIncrementCapsDraft.lean` (private staged draft, not shipped), SHA-256 `ca8a29d2bb7c1d60a8d52924da97df4d9011e5660eeb62be36d2df25edc154e1`, matching the current builder handoff. Its direct staged dependency `QLearningHistoryAdaptationDraft.lean` (private staged draft, not shipped) is SHA-256 `766309449c858a91456f82499c75e4de9c2af11fc8d6268f37f4e59815562c4f`; that artifact was freshly built with the exact 12-module natural-history dependency chain in an isolated local audit directory (not shipped).

Freshly compiled the exact increment-cap source to an isolated local audit directory (not shipped). All four public exports were probed; each reports only `propext`, `Classical.choice`, and `Quot.sound`. No compilation repairs were required.

## Statement review

- `qRow_abs_centered_le` uses only that a finite-distribution expectation of a value in `[0,H]` is also in `[0,H]`; every sampled value is therefore within H of the row mean. No strict positivity or support assumption is needed.
- `qRowVariance_le_sq` bounds every squared centered value by H² and averages over the actual transition row. It is intentionally a coarse H² cap, not the sharper H²/4 bound.
- `qPaddedIncrement_abs_le` concerns the actual iterate-dependent increment `D_t=V_t(Y_{t,s,a})−P_{s,a}V_t`, not the source's weighted comparator fluctuation. It uses pathwise bounds on the actual `qLearningIterate` for the fixed sample array. The rate premise is exactly `0≤η_k≤1` for `1≤k≤T`, with no condition on unused η₀ or rates after T. For `t≥T`, `qPaddedIncrement` is zero; consequently T=0 gives the all-zero sequence.
- `qValueBefore_rowVariance_le` proves the pointwise actual-row variance cap for `V_t` when `t<T`. This parameter range follows the update convention: the fresh row used for D_t is layer t, while V_t only depends on preceding updates. The bound holds for every data array, so it can later be used as an a.e. bound under the actual sampling law.

The source of the Q-learning Freedman comparison fluctuation instead uses deterministic `V⁺`/`V⁻` and source weights `γ η_i^(u)`; it is a different sequence. These caps do not prove its schedule-weight bounds or its Freedman event.

## What these caps do not yet prove

The existing natural-history square identity states that the conditional second moment of the padded `D_t` under its smaller increment-generated history is the conditional expectation of `qRowVariance(V_t)` under that history. To derive a deterministic H² cap there, a later lemma must apply conditional-expectation monotonicity to the pointwise bound and use integrability/constants correctly. Summing over the T possible increments would then give the coarse predictable-sum cap T H². This file does not itself prove that conditional transfer, sum cap, increment-history Freedman application, or any probability/rate theorem. The source's `V*` or `V±` weighted fluctuations remain separate.

No source-level issue found in the interval, rate, zero-padding, or actual-versus-source fluctuation scope.

Production integration: the reviewed source declarations and proofs compile in the project export with qualified production imports and updated staging-only comments where applicable. The full project audit checked 2,970 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.

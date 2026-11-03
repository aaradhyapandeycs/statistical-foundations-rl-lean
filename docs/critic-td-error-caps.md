# Source review: TD deterministic error and increment caps

No compiler was used. Reviewed `.local/TDErrorCaps.lean`, SHA-256 `952f7f0f94634574f55b6ccc6cc97c8a535d4acfe0f62e71f80f141c418e0983`, against `.local/TDErrorUnroll.lean`, `Formalization/ModelFree/TDLearningWeights.lean`, and the pinned source `generative_model_model_free.tex:331–410`, especially equations `eq:TD-L1-norm` and `eq:defn-eta-k-t`.

## Findings

- `tdErrorPropagate` applies the transition at update `start+1` through update `t`, with the latest transition acting outermost. The norm proof follows that chronological recursion by induction. It bounds the genuine Pi/sup norm of the state vector directly using the true policy-row expectation; it does not rely on an ambiguous matrix-product norm convention. Since each row of `Pπ` is a probability distribution, `‖Pπ U‖∞≤‖U‖∞`, giving the scalar factor `1−η_i(1−γ)` for each update when `0≤η_i≤1` and `0≤γ<1`.
- The product in `tdErrorPropagate_norm_le` is over exactly `start+1,…,t`. The helper `tdRateWeight` uses `η_k ∏_{i=k+1}^t(1−η_i(1−γ))` for positive `k≤t`, matching the source's `η_k^(t)` and the staged source-form theorem for the propagated innovation. The `tdWeightedErrorIncrement_norm_le` envelope adds the `2‖V_(k−1)‖∞` bound for sample-minus-row-mean noise, yielding the source-shaped `2 γ η_k^(t) ‖V_(k−1)‖∞` bound.
- The actual iterate-bound wrappers require learning-rate hypotheses only for `1≤i≤t`. They replace the unused `η₀` by zero and prove the iterate unchanged from agreement on used update indices. Thus no spurious condition on η₀ is introduced. The weighted-increment cap similarly assumes positive, in-range `k` and rates only on the actual prefix through t.
- The cap uses the real initial range `0≤V₀≤1/(1−γ)` and the actual iterate bounds. It is deterministic for every sample array, not merely almost everywhere.

No source-level mismatch found in propagator order, positive-index weight, norm, or the treatment of η₀. These are deterministic magnitude bounds only. They do not establish conditional centering, conditional variance, a predictable variance-sum cap, Freedman applicability, source step-size schedule bounds, or a probability/rate theorem.

## Independent exact-source compilation and axiom probe

After the source review, the exact target and staged dependencies were rebuilt into `.local/td-error-caps-independent-audit`: `.local/TDErrorDecomposition.lean` SHA `c0a838360290c7d47e16a0228d5a4ecfbfee06ddfc354a9e2ba4df07241a51fe`, `.local/TDErrorUnroll.lean` SHA `495d294dae15f39fd1fe7a4f07fc7a202eec9dddf0686a15fd36f56555538e48`, and `.local/TDErrorCaps.lean` SHA `952f7f0f94634574f55b6ccc6cc97c8a535d4acfe0f62e71f80f141c418e0983`. Compilation succeeded. All eight target exports were probed and each uses only `propext`, `Classical.choice`, and `Quot.sound`.

Production integration: the reviewed source declarations and proofs compile in the project export with qualified production imports and updated staging-only comments where applicable. The full project audit checked 2,970 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.

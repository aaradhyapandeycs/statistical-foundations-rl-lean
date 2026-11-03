# Independent review: fixed-terminal TD natural history

Reviewed `.local/TDTerminalHistory.lean`, SHA-256 `32a66e31d1d5f48d52211f2d7da1e0b4027fb0221c3d7f500299eeffd92b3d1a`. I did not find a separate builder handoff document for this file; this review and compile are bound to the source hash above.

## Source findings

The bridge preserves the sample-time convention: `tdPastSigma T n` contains used coordinates at source times `1,…,n`, excludes the stored time-zero coordinate, and the increment at filtration index n is actual source (Z_{n+1}^t) using the sample coordinate (n+1). The premise `n<T` validates that coordinate. For fixed `t≤T`, `tdTerminalIncrement_zero_after` proves the actual source innovation is exactly zero for `n≥t`; `tdTerminalIncrement_strong_nextPast` handles both active and padded indices, using the actual row representation when `n<t` and zero otherwise.

The natural-history inclusion is correctly oriented: every prior increment with index `j<n` is measurable in the actual sample prefix through `j+1≤n`, so its generated sigma algebra is included in `tdPastSigma T n`. The past-prefix conditional mean zero is already derived from the actual fresh row; the tower property transfers this to the increment-generated history. For the active square, the bridge also uses the tower property, but importantly retains the outer conditional expectation of the random raw-prefix variance vector under the smaller natural history. It does not silently claim that the prefix-dependent (V_n) variance is measurable in the natural increment history. This square theorem has `n<t`; padded-tail zero is separately proved and the terminal predictable sum uses only active indices.

No hidden bounded-iterate, step-size, or concentration premise is added by this history bridge. The source samples and fixed terminal remain explicit. No source-level mismatch found in padding, adaptation, filtration inclusion, centering, or the outer-expectation variance identity.

## Independent compile and axioms

Freshly compiled the 11-module staged closure into `.local/td-terminal-history-audit-32a66e31/`: `TDCausality`, `TDErrorDecomposition`, `TDConditionalMoments`, `TDCrossCovariance`, `TDErrorUnroll`, `TDErrorCaps`, `TDLinearRowVariance`, `TDPropagatorRows`, `TDWeightedVariance`, `TDVarianceSum`, and `TDTerminalHistory`. The qualified production `Formalization.Probability.FreedmanNaturalHistory` and its production dependencies were reused from existing project artifacts, not rebuilt.

All nine declarations/definitions exported by `TDTerminalHistory` were probed: fresh-coordinate measurability, fresh-indicator strong measurability, raw-row strong measurability, terminal zero padding, terminal next-prefix adaptation, natural-history inclusion, prefix conditional centering, natural-history tower centering, and natural-history conditional square. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. This is focused staged evidence, not a production integration claim.

## Production integration

The reviewed result is now integrated as `Formalization/ModelFree/TDTerminalHistory.lean`. Its proof and declaration bodies match the reviewed staged source; imports and status comments were adjusted. The complete project check compiled 234 modules and audited 3,148 project declarations, using only `propext`, `Classical.choice`, and `Quot.sound`. This does not change the scope or imply the final source theorem.

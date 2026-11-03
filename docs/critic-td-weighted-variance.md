# Independent review: fixed-terminal TD weighted variance

Reviewed `.local/TDWeightedVariance.lean`, SHA-256 `9c99c1eaa1f39bbff926c4da0c4f66efcb5760e1d3e63bc92ada80d8203d0557`, against source equation `eq:TD-Zk-defn` and `eq:TD-var-Zk-upper-bound-each-term` in `generative_model_model_free.tex` and the staged sampling/propagator definitions.

## Semantic checks

The theorem keeps the total draw horizon `T` and fixed final time `t` separate, requiring `k+1≤t≤T`. Its `tdSampledWeightedIncrement` is the actual `tdWeightedErrorIncrement` evaluated on `tdSamplesExtend`; update `j=k+1` uses `tdCenteredRowNoise` built from the old iterate `V_k` and the actual draw at array coordinate `k+1`. `tdSamplingLaw` contains coordinates `0,…,T`, with coordinate zero unused by the update. The condition `k+1≤t≤T` ensures the fresh coordinate exists and the prefix conditioning is on the first k actual updates, matching source update j conditioned on time j−1.

The row identification equates the actual fixed-terminal innovation with a deterministic linear combination of actual fresh-row noises. Its coefficient is `tdWeightedPropagatorRow M π η t (k+1) s r = γ η_{k+1} R_{k+1,t}(s,r)`: the terminal remains fixed, the propagation uses chronological updates `k+2,…,t`, and `γ η_{k+1}` occurs once. The row mass is `γ tdRateWeight γ η t (k+1)`, where the rate weight contains `η_{k+1}` and the suffix contraction product. Applying the row to a vector supplies a second factor `γ η_{k+1}`; their product in the variance proxy is exactly `γ² tdRateWeight γ η t (k+1) η_{k+1}`. No extra or missing η or γ factor was found.

Conditional centering is derived from the actual raw-row centering theorem and finite linearity under the actual sampling law. The conditional square identity retains the exact squared row coefficients and the actual row variances of the predictable `V_k`; together with conditional mean zero it is the conditional variance. The final inequality applies the nonnegative-row proxy to those same coefficients and uses the exact propagated row mass/action identities. Its only rate premise is `0≤η_i≤1` for positive `i≤t` (plus `γ≥0` from the MDP); it assumes no estimate of the target variance, no large-T regime, and no terminal-independent martingale process. It is the per-increment source proxy, not a cumulative variance cap or Freedman result.

## Fresh staged compile and axioms

The nine-module staged closure was freshly compiled into `.local/td-weighted-variance-audit-9c99c1ea/`; production imports came from existing project artifacts and were not rebuilt. The rebuilt staged modules, in dependency order, were `TDCausality`, `TDErrorDecomposition`, `TDConditionalMoments`, `TDCrossCovariance`, `TDErrorUnroll`, `TDErrorCaps`, `TDLinearRowVariance`, `TDPropagatorRows`, and `TDWeightedVariance`. All six declarations/definitions exported by the target file were probed: the sampled-increment definition, actual row identity, linear-row centering, sampled-increment centering, exact conditional square, and variance proxy. Every probe reports only `propext`, `Classical.choice`, and `Quot.sound`. This is focused staged evidence, not production integration.

## Production integration

The reviewed result is now integrated as `Formalization/ModelFree/TDWeightedVariance.lean`. Its proof and declaration bodies match the reviewed staged source; imports and status comments were adjusted. The complete project check compiled 234 modules and audited 3,148 project declarations, using only `propext`, `Classical.choice`, and `Quot.sound`. This does not change the scope or imply the final source theorem.

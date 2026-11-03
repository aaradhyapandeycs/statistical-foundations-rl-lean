# Source policy-evaluation sample-size assembly

Source: `source/upstream/tex/chapters/generative_model_model_based.tex` lines 141–155 (`thm:model-based-policy-eval`), 471–478 (`eq:Bernstein-Vl`), and 622–634 (`eqn:ice-cream`); SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

The printed theorem assumes `0 < ε ≤ 1/(1−γ)` and `0 < δ < 1`; for some sufficiently large universal `c₀`, it requires **per-state** sample count

```text
N ≥ c₀ log(S/(δ(1−γ))) / ((1−γ)³ ε²).
```

The logarithm is exactly `log(S/(δh))`, where `h=1−γ`; the constant multiplies the logarithm outside it, and neither the logarithm nor `c₀` depends on `N`. The algorithm requires positive integer `N`. The source does not state a numerical `c₀`; the value 720 below is a sufficient arithmetic constant for the staged concentration event and conditional radius, not a claim that the source chose that value.

`.local/PolicyEvaluationSampleAssembly.lean` proves the following independent ingredients:

1. `valueEstimator_eq_true_of_subsingleton` gives exact equality for the actual empirical policy-evaluation estimator at every data realization when the state type is a subsingleton (in this MDP it is nonempty, so `S=1`). It uses the actual row residual and does not assume exactness or a good sampling event. This handles the case where the printed theorem's log tends to zero near `γ=0`, `δ=1` and direct absorption of an additive log constant is impossible.
2. `source_selected_depth_log_bound` proves for `S≥2`, `0<h≤1`, and `0<δ≤1`, with `m=⌈log(e/h)⌉`,
   `2 log(4 S (m+1)/δ) ≤ 10 log(S/(δh))`.
   The `m+1` is required because the staged Bernstein event covers every `0≤l≤m`. The argument proves `m+1≤3/h`, sets `X=S/(δh)≥2`, bounds the event log argument by `12X≤X⁵`, and applies log monotonicity. There is no `N` inside either logarithm.
3. `source_sample_budget_from_printed_log` proves that the printed sample condition with the concrete universal constant `c₀=720`, for `S≥2`, implies both `N≥64β/h` and `3√(8β/(h³N))≤ε`, with `β=2 log(4S(m+1)/δ)` and the printed `0<ε≤1/h` range. It is deterministic arithmetic; its positivity and real `N` hypotheses are explicit and later application must coerce the actual positive natural sample count. The factor `h³ ε²` is outside the logarithm, exactly as printed.

For `γ=0`, the separately staged auxiliary result proves empirical and true auxiliary vectors are identical at all levels and all samples; this can be used regardless of `S` and avoids division by γ. At `ε=1/h` the arithmetic remains valid. For `S=1` the exactness result applies instead of requiring the logarithmic comparison; at `S≥2` the log is bounded away from zero. The conclusions here do not prove a probability event, the required terminal residual estimate, an assembled source radius, or the final theorem. They must be connected to reviewed actual-law concentration, the deterministic recursion and its terminal condition, then independently reviewed and validated as exports.

Validation: `bash scripts/lean-local.sh .local/PolicyEvaluationSampleAssembly.lean` passed with one nonsemantic `unnecessarySeqFocus` tactic-style warning at line 94. An exact-source temporary probe of one-state exactness, the selected-depth log bound, and the printed-log budget implication reported only `propext`, `Classical.choice`, and `Quot.sound`. Staged source SHA-256 `f408a6050eb96cfc7b4c5ab95ff1d22f0c556ad6b0a3a7783164642d03accc5b`. Independent review and integrated-export validation remain outstanding.

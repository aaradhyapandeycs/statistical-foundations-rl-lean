# Main policy-learning sample arithmetic handoff

Staged source `.local/PolicyLearningMainSampleArithmetic.lean`, SHA-256 `e3f6d47f3ec0bf8b7869cb1586ae2199ea2aa23a52ede01a1f0cab5984cea1b7`; plan `docs/builder-policy-learning-main-sample-plan.md`. Production import is `PolicyEvaluationSampleAssembly`.

`mainSample_log_comparison` proves `2 log(16 K/(hδ)) ≤ 10 log(K/(h² ε δ))` for K≥2, h∈(0,1], 0<δ<1, and 0<ε≤1/h. This uses exactly the printed main logarithm, including the N factor when K=SAN. `mainSample_scalar_bounds` proves that the printed budget with c=10240 and a proved β≤10L imply both `720β/h ≤ N` and `32 sqrt(β/(Nh³))≤ε`. The latter theorem is scalar and accepts n=0 only in the degenerate totalized case; it does not purport to construct empirical samples there.

At K=1 the log comparison is not valid with a uniform multiplier; the plan explains the singleton state/action exactness case needed for the main theorem. Positive N remains a source sampling/log-domain hypothesis, because N=0 vacuously satisfies the unguarded totalized threshold. The current files do not prove this singleton case or the final probability theorem. Exact source compilation and both axiom probes succeeded with only standard axioms. Independent source review and production integration remain.

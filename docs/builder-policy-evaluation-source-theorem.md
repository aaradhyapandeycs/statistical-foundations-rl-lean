# Staged source-shaped policy-evaluation theorem

Source: `source/upstream/tex/chapters/generative_model_model_based.tex:141–155`, `thm:model-based-policy-eval`, and its proof at lines 413–634; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

`.local/PolicyEvaluationSourceTheorem.lean` compiles a candidate source-shaped theorem for every finite valid discounted MDP, every fixed stationary randomized policy, and every natural sample count `N`, with `0<δ<1`, `0<ε≤1/(1−γ)`, and

```text
720 log(S/(δ(1−γ))) / ((1−γ)³ ε²) ≤ N.
```

The stated conclusion supplies a proof `hN : 0<N` and says that the **actual** product sampling law assigns strictly greater than `1−δ` real probability to sup-norm error at most `ε` for `valueEstimator M π N hN` versus `M.trajectoryExpectedValue π`. The source asks for at least `1−δ`; strict success is stronger. The constant 720 witnesses the source's unspecified sufficiently large universal constant. The logarithm, its denominator, and the placement of ε and the horizon match the printed statement. It is an `NS`-sample algorithm because `N` samples are taken for each state.

`source_sample_count_pos` derives `0<N` from the printed bound and the source's existing positive-δ/ε and MDP assumptions: since the state space is nonempty, `S/(δ(1−γ))>1`, the budget is positive. The main conclusion existentially supplies this proof witness because the estimator's type requires it; no independent sample-positivity premise is imposed. The policy is fixed before drawing samples; no additional independence or approximation hypotheses occur.

The proof splits on `S≤1`. Because MDP states are nonempty this is the source's `S=1` case, where the true and empirical transitions act identically and the estimator is exactly correct for every sample. For `S≥2` it applies the staged printed-log budget arithmetic to get both the high-sample cutoff and radius ≤ε, then transfers the staged high-sample actual-law event by inclusion. The latter's common-event proof handles all levels, and its `γ=0` branch uses exact equality; no intersection of separately probable events is used. The inclusive `m+1` levels enter the explicit Bernstein logarithm, while the top-level budget has precisely the printed `log(S/(δ(1−γ)))`.

## Validation and status

Staged dependency source hashes checked before building: `PolicyEvaluationHighSample.lean` `b8f4dd90e9571d730eb0203752e3299c8d4ee3c0cbabdfdd6961037f096ac601`, `PolicyEvaluationSampleAssembly.lean` `f408a6050eb96cfc7b4c5ab95ff1d22f0c556ad6b0a3a7783164642d03accc5b`, and its high-sample dependency `PolicyEvaluationTerminalError.lean` `29c50df335bf18e75083d8628817f16d5f076f6eb32e63465ed227752e306145`. These files were built sequentially to project-owned staged `.olean` files, then `lake env bash -c 'export LEAN_PATH="$PWD/.local:$LEAN_PATH"; lean .local/PolicyEvaluationSourceTheorem.lean'` passed. The exact source with two appended `#print axioms` compiled, and both `source_sample_count_pos` and `valueEstimator_source_sample_bound` reported only `propext`, `Classical.choice`, and `Quot.sound`. The sample-assembly dependency build emitted one tactic-style linter warning; the top-level file emitted no diagnostic. Top-level staged SHA-256 `5203c0716ed90521be7ce2a9448b2a8f1b5c68e958ccb37fb274af52c80fc73a`.

This is a staged candidate, not yet an independently reviewed or production-export completion claim. The high-sample and sample-assembly exact staged sources are under independent review; the full transitive source semantics, probability event, quantifiers, hashes, actual production import closure, full build and exported axiom audit must be independently checked after landing. No whole-monograph completion is implied.

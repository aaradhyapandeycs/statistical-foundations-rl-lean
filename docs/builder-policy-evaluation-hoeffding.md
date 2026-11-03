# Model-based policy evaluation: conservative Hoeffding bound

`.local/PolicyEvaluationHoeffding.lean` proves a high-probability value-estimation bound for the **actual direct policy-row sampling law and plug-in estimator** from `Formalization.Generative.ModelBasedPolicyEvaluation`. It uses the fixed true trajectory value as the singleton vector in the source Hoeffding inequality, derives a statewise union bound, and composes the resulting residual control with the staged deterministic perturbation theorem. The result has an explicit `(1−γ)⁻⁴` sufficient sample size and is weaker in horizon dependence than the source Chapter 3 policy-evaluation theorem's `(1−γ)⁻³` guarantee. It is a staged contribution pending independent review and integration; it is not the source's sharp theorem.

## Source and actual algorithm

The source's direct policy-evaluation algorithm samples N independent next states from the policy-induced transition row `P_π(·|s)` for each state and computes the empirical plug-in value (`generative_model_model_based.tex:78–130`). The source Hoeffding bound for a fixed finite nonnegative family is `prelim.tex:916–949`. Its policy-value theorem `thm:model-based-policy-eval` is model-based lines 142–155 and asks for sample complexity with effective-horizon exponent three.

The integrated `samplingLaw M π N` is the actual independent product over `(s,i)` of the corresponding true policy-row distributions; `empiricalPolicyRow` is the empirical frequency vector and `valueEstimator` is the unique empirical policy Bellman fixed point. The policy π is fixed before sampling, though it may be any stationary randomized policy; the theorem does not allow π to be selected from the same data.

The empirical evaluation module embeds the policy-averaged reward and empirical policy kernel as action-independent rows. The original MDP generally has action-dependent rewards, so directly assuming its reward equals that embedded model's would be wrong. The staged `policyCollapsedModel` instead embeds the **true** policy-averaged reward and true policy transition kernel in the same form. `policyCollapsedModel_bellman` proves its policy Bellman operator equals the original's, and `policyCollapsedModel_trajectoryValue` proves its actual infinite-trajectory policy value is the original true value. The staged `valueEstimator_perturbation` then applies the independently reviewed deterministic perturbation result to this true collapsed model and the actual empirical evaluation model. Its residual is exactly `(P̂_π−P_π)V^π`.

## Results and constants

All results are in `StatisticalRL.ModelBasedPolicyEvaluation`. For every admissible finite MDP M, fixed stationary randomized π, integer `N>0`, and `0<δ<1`, write `S = card State`, `V = M.trajectoryExpectedValue π`, and

```text
R = ‖V‖∞ sqrt(log(2S/δ)/(2N)).
```

- `samplingLaw_stateRow` proves that each vector of N draws at one state has exactly the N-fold iid product law of the true policy row, deriving it from the actual global sampling law and its joint independence; no row-law equality is assumed by the final theorem.
- `policyHoeffdingRadius_eq` identifies the instantiated singleton-family source Hoeffding radius (with confidence `δ/S`) with the displayed R.
- `valueEstimator_hoeffding` proves under `samplingLaw M π N` that, with probability **strictly greater than** `1−δ`,

  ```text
  ‖Vhat^π − V^π‖∞ ≤ γ R/(1−γ).
  ```

  The true trajectory value is nonnegative by its proved source reward bounds. Each row's fixed-vector strict failure probability is below δ/S; the finite union and an event inclusion give the simultaneous bound. No concentration event or target value error is an input.
- `truePolicyValue_norm_bound` proves `‖V‖∞≤1/(1−γ)` for the actual trajectory value.
- `valueEstimator_hoeffding_uniform` eliminates the unknown norm and proves, with the same strict success probability,

  ```text
  ‖Vhat^π − V^π‖∞ ≤ γ/(1−γ)² · sqrt(log(2S/δ)/(2N)).
  ```

- `valueEstimator_hoeffding_sample_bound` proves that for any ε>0, if

  ```text
  N ≥ log(2S/δ)/(2 ε² (1−γ)⁴),
  ```

  then the actual estimator's sup-norm error is at most ε with probability **greater than** `1−δ`. The proof uses `γ≤1`; it retains the factor `1/2` from Hoeffding. This exact sufficient condition is not the source theorem's sharper condition and has no hidden universal constant. The source's extra upper bound `ε≤1/(1−γ)` is unnecessary for this valid conservative result; no source theorem is claimed with a modified signature.

The inequality is non-strict and the probability is strict; zero discount, zero value norm and N=1 are covered. `N>0` is explicit because empirical frequencies divide by N. The finite nonempty-state condition is obtained from M's source MDP fields. No empirical variance or Bernstein result is used.

## Validation and integration boundary

The exact staged source was copied unchanged to a temporary probe and compiled with nine appended `#print axioms`. The search path included `.local` and the project/package build artifacts, and the staged `PolicyEvaluationPerturbation.olean` was compiled from the exact staged perturbation source. All nine declarations—`policyCollapsedModel_bellman`, `policyCollapsedModel_trajectoryValue`, `valueEstimator_perturbation`, `samplingLaw_stateRow`, `policyHoeffdingRadius_eq`, `valueEstimator_hoeffding`, `truePolicyValue_norm_bound`, `valueEstimator_hoeffding_uniform`, and `valueEstimator_hoeffding_sample_bound`—use only `propext`, `Classical.choice`, and `Quot.sound`. The exact source/axiom probe compiled with no diagnostics.

The local source currently imports `PolicyEvaluationPerturbation` by its staging name. After independent review and integration of that dependency, update the import to its actual project path, independently check the integration diff, rebuild the affected project and audit the integrated export. The sharp variance/resolvent control and source sample-complexity theorem remain open.

SHA-256:

- `.local/PolicyEvaluationHoeffding.lean`: `75b1c4e40ad366e07e88d3b9fab10650da84e0ab7722c3b5e04fd81bd14d4d30`.
- `.local/PolicyEvaluationPerturbation.lean`: `eb8844a5cb2f05a5ea44c2b48a9f9182947731e86ec66d57890e2cf800dfff38`.
- `Formalization/Generative/ModelBasedPolicyEvaluation.lean`: `fe368676ff1a9b30b988112ae3478b3ed46abf1949c66a2169751fb60560aa53`.
- `Formalization/Probability/EmpiricalHoeffdingFamily.lean`: `0b8bf547984a749623012f9a6a19ffe92ffa9c10f8a69d6b4abf139c794dc12d`.
- Source `generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

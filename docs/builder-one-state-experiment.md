# Staged one-state generative experiment and Q-estimation obstruction

`.local/OneStateExperiment.lean` constructs the actual independent one-sample-per-row experiment for `S=1`, `A=16` and composes it with the actual infinite-trajectory one-state Q formula and the parameter-feasibility theorem. Its main declaration proves, for each positive proposed `c`, feasible source parameters and one measurable estimator whose strict-error probability is zero for **every** admissible one-state model at `γ=2/3`, including all known reward tables. This is a staged formal obstruction under the project’s explicit experiment and source interpretations; it awaits independent source/statement/code review and integrated compilation. It is not presented here as an author-approved erratum or a reviewed full-source theorem refutation.

## Source and exact model

The source gives global finite state and action carriers, bounded deterministic and fully known reward, and known discount (`prelim.tex:31–45`, model-based chapter `:15–31`); defines Q by forcing the first action and following the policy thereafter (`prelim.tex:114–123`); and states Theorem `theorem:azar` with `SA≥16`, `γ∈[2/3,1)`, strict positive accuracy, and N independent samples per state-action pair (`generative_model_model_based.tex:1438–1464`). This staged model fixes the source-permitted `S=1`, `A=16`, `γ=2/3`, `N=1`; A=16 also satisfies the earlier policy-learning A≥2 condition.

`OneSampleIndex := (Fin 1 × Fin 16) × Fin 1` and `OneSampleData := OneSampleIndex → Fin 1`. Thus every state/action pair has exactly one sample index. `oneStateGenerativeLaw M` is `Measure.pi` of `(M.transition s a).rowMeasure` over all these indices, on the finite product measurable space. `oneStateGenerativeLaw_probability` proves it is a probability law; `oneStateGenerativeLaw_marginal` proves each coordinate has the actual corresponding model transition law; `oneStateGenerativeLaw_independent` proves mutual independence of the full indexed sample family. The samples are necessarily degenerate on a one-state carrier, but independence is established for the genuine product law, not merely inferred from an unspecified measure. `oneStateExampleMDP` is an actual admissible model with discount `2/3`, ensuring the relevant class is inhabited.

## Estimator, target and quantifiers

`oneStateExperimentEstimator` is the same known-input rule for all models and data:

```text
Qhat(r, γ, data)(s,a) = r(s,a) + γ max_b r(s,b)/(1−γ).
```

It ignores data and does not take the hidden transition kernel or target Q as an input. `oneStateExperimentEstimator_measurable` checks measurability in data for each known reward and discount; the stronger `oneStateExperimentEstimator_joint_measurable` checks joint Borel measurability in reward, discount and data (Lean real division is total, so this even holds at discount 1; admissible MDPs have discount below 1).

The target in `oneStateExperimentEstimator_failure` is the actual forced-first-action infinite-trajectory Q of the explicitly constructed optimal greedy policy, not a stipulated value or unknown kernel supplied to the estimator. The imported trajectory bridge proves that the same policy attains the optimal Bellman solution and dominates every stationary randomized policy's actual trajectory Q. The loss is the finite sup norm of the full state-action Q-array. The event `{data | ε < ‖Qhat − Q*‖}` has real probability exactly zero for every `ε≥0` and **every** `DiscountedMDP (Fin 1) (Fin 16)` (arbitrary valid transitions, reward and discount), with no conclusion assumed.

The final theorem `oneState_theorem37_ii_obstruction` has the explicit order:

```text
∀ c > 0, ∃ ε > 0,
  [source strict accuracy, γ bounds, SA≥16 and N=1 sample bound] ∧
  [∃ an admissible model at γ=2/3] ∧
  ∃ one estimator,
    [data measurability and joint known-input measurability] ∧
    ∀ admissible M with γ=2/3,
      P_M(ε < ‖Qhat(M.reward,M.discount,data) − Q*_M‖∞) < 1/4.
```

The known reward varies with M and is supplied as an observable input to this **one** estimator; it is not frozen across the model quantifier. The theorem includes an explicit inhabited-model witness and uses the already proved `oneState_theorem37_hypotheses_feasible` rather than assuming the sample bound or feasible ε. As all MDP validity fields are those of `DiscountedMDP`, rewards lie in `[0,1]`, transition rows are normalized and carriers are nonempty. The event probability is `Measure.real` for the actual product law. The result targets stationary-policy trajectory Q as represented by the reviewed optimal-trajectory module; no additional nonstationary policy-class result is asserted here.

## Verification and remaining integration

The exact staged source was copied to a temporary probe, appended with eight `#print axioms` commands, and compiled without diagnostics using the project's pinned `.local/lean` and project/dependency search paths with `.local` additionally at the front. Its imports were compiled project artifacts and a local `.local/OneStateTrajectory.olean` compiled from the exact preceding staged source. All of `oneStateGenerativeLaw_probability`, `oneStateGenerativeLaw_marginal`, `oneStateGenerativeLaw_independent`, `oneStateExampleMDP_discount`, `oneStateExperimentEstimator_measurable`, `oneStateExperimentEstimator_joint_measurable`, `oneStateExperimentEstimator_failure`, and `oneState_theorem37_ii_obstruction` report only `propext`, `Classical.choice`, and `Quot.sound`.

The first import currently reads `import OneStateTrajectory` because the dependency is staged locally. On integration, first independently review and integrate the trajectory dependency, replace that import with its actual project module path, then review the exact integration diff, rebuild the affected project and audit the integrated exports. This note does not assert an unqualified whole-paper theorem correspondence, resolve the author's intent regarding the source quantifiers/standing conventions, or certify proof completion beyond the displayed result.

SHA-256:

- `.local/OneStateExperiment.lean`: `e7b4220fab2b6495905667e1530e1f32d2e8ce564ac7bdc31f0299cf088ecc8f`.
- `.local/OneStateTrajectory.lean`: `091d881d496d1709115cb088a749d708633513c45bf84154ac534c93a02133d1`.
- `Formalization/Obstructions/OneStateParameters.lean`: `2be78dda039c300ebcc4455658994b8b0495c7f5da6ef31c1db20fb27b1586ba`.
- `Formalization/Probability/EmpiricalRow.lean`: `6e87c90ff1150f7053845acff92d60a5c35035c7a78adcd394e0da5f3d9dc154`.
- Source `prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
- Source `generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

# Intermediate policy-evaluation variance budget

`.local/PolicyEvaluationVariance.lean` proves a source-derived deterministic variance self-bound for actual infinite-trajectory policy values, then bounds a finite discounted variance recursion and its infinite limit by an explicit value-dependent potential. The infinite budget is the unique solution of its discounted variance Bellman equation. This is an **intermediate** toward the sharper horizon-three policy-evaluation result; it does not establish the matrix-resolvent or Jensen/square-root bound, empirical-to-true resolvent comparison, concentration composition, or the source's sample-complexity theorem. Independent review and integration remain pending.

## Source reconstruction and dependency path

For `V=V^π`, `r=r_π`, `P=P_π`, and `γ∈(0,1)`, the source rewrites the row variance using `V=r+γPV` and obtains (`generative_model_model_based.tex:321–334`)

```text
γ² Var_P(V) ≤ (γP−I)(V²) + 2 V r.
```

It then applies the positive true resolvent and obtains a variance budget at most `2‖V‖∞²/γ²` (`eq:I-gamma-P-Var-bound`, lines 335–344), followed by Jensen's square-root step (`eq:Jensen-I-gamma-P-Var`, lines 305–315) and the true-resolvent bound (`eq:lemma-VarP-V-bound`, lines 345–350). The subsequent comparison of empirical and true resolvents in that section is presented heuristically; it is not assumed in the staged result. The complete sharp argument needs a rigorous empirical-versus-true resolvent comparison, Bernstein control of the actual residual, and the indicated regime/sample arithmetic in addition to the true-kernel variance budget.

The code uses the actual expected infinite return `M.trajectoryExpectedValue π`, with its integrated reviewed trajectory-to-Bellman bridge and bounded reward properties. `evaluationPolicyReward` is the policy-weighted reward, and `evaluationPolicyVariance` is the population variance under the actual policy-induced transition row, not the variance of the whole random return. State and action carriers are finite, M is an admissible discounted MDP with reward in `[0,1]`, and π is any fixed stationary randomized policy. No statistical event, desired convergence rate, matrix inverse, or extra model premise is assumed.

## Proved declarations

All declarations are in `StatisticalRL.DiscountedMDP`.

- `evaluationTrajectory_bellman` gives the exact true trajectory-value Bellman identity.
- `evaluationPolicyVariance_identity` proves the source's exact second-moment algebra after multiplying by γ²:

  ```text
  γ² Var_P(V)(s) = γ² P(V²)(s) − V(s)² + 2 V(s) r(s) − r(s)².
  ```

- `evaluationPolicyVariance_selfBound` proves the displayed source inequality above without dividing by γ, so it includes γ=0.
- With `B=‖V‖∞`, `evaluationVariancePotential` defines `W(s)=2B V(s)−V(s)²`. `evaluationVariancePotential_bounds` proves `0≤W(s)≤B²`, and `evaluationVariancePotential_super` proves

  ```text
  γ² Var_P(V)(s) + γ P W(s) ≤ W(s).
  ```

  This uses `0≤V≤B`, nonnegative policy reward, and the actual true-value Bellman equation. It is a tighter potential estimate than the source's final `2B²` variance budget after scaling, but no stronger source theorem is claimed solely from this observation.
- `discountedPolicyVariancePartial` starts at zero and recursively sets `U_{n+1}=γ² Var_P(V)+γ P U_n`. Consequently, mathematically it expands to `γ² Σ_{t=0}^{n−1}γ^t P^t Var_P(V)`; the code proves the recursion, not a separate expansion lemma. `discountedPolicyVariancePartial_bounds`, `_le_norm_sq`, and `_mono` prove every partial budget is nonnegative, bounded by W and B², and increases with n.
- `discountedPolicyVarianceBudget` is the pointwise supremum of those partial budgets. `_tendsto` proves the monotone finite recursions converge to it; `_bounds` and `_le_norm_sq` retain `0≤U≤W≤B²` in the limit. `_bellman` proves `U=γ² Var_P(V)+γ P U`, and `_unique` proves any other real-valued state function satisfying that equation equals U by the existing policy Bellman contraction. Thus the budget is not defined by assuming the desired bound.

All these results are valid for `0≤γ<1`, including the zero-discount endpoint. They give a direct self-bounding ingredient; they do **not** formally identify U with `γ²(I−γP)⁻¹ Var_P(V)`, even though uniqueness supplies the natural route for such a bridge. They also do not prove a finite-sum expansion or the source Jensen bound for `P`-resolvent applied to `sqrt(Var_P(V))`. Those missing links must be supplied and reviewed before using this module to claim the horizon-three concentration theorem.

## Verification and identity

The exact staged source was copied unchanged to a temporary probe and compiled via `bash scripts/lean-local.sh` with eleven appended `#print axioms` commands. The source and probes compiled without diagnostics. `evaluationTrajectory_bellman`, `evaluationPolicyVariance_identity`, `evaluationPolicyVariance_selfBound`, `evaluationVariancePotential_bounds`, `evaluationVariancePotential_super`, `discountedPolicyVariancePartial_bounds`, `discountedPolicyVariancePartial_mono`, `discountedPolicyVariancePartial_tendsto`, `discountedPolicyVarianceBudget_bellman`, `discountedPolicyVarianceBudget_le_norm_sq`, and `discountedPolicyVarianceBudget_unique` all use only `propext`, `Classical.choice`, and `Quot.sound`. This is a focused staged source check against existing integrated dependencies, not an integrated project build.

SHA-256:

- `.local/PolicyEvaluationVariance.lean`: `f25b76fadce9e452abe3375d2b8b5cf003df748ab6d737529cbe58b1b039d33d`.
- `Formalization/MDP/PrefixValueBridge.lean`: `bd286567aa059c3e5fb293f1943eb06bd2e3d79c8dc9484d8a73195a2db16e89`.
- `Formalization/Probability/Variance.lean`: `541714ed6173402131bece633476308c1c832f31d0cbb46534cc55f48dcd9553`.
- Source `generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

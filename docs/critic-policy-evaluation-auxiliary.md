# Independent review: policy-evaluation auxiliary vectors

**Verdict: PASS for the stated true/empirical auxiliary definitions, actual-value base cases, nonnegativity, Bellman equations, and conservative growth bound.** This module does not prove the source's sharper growth factor, its simultaneous Bernstein event or the chapter's high-probability sample theorem. The estimates are staged infrastructure pending integration; this is not an author-approved frozen theorem or full source-proof certification.

Reviewed `.local/PolicyEvaluationAuxiliary.lean` at SHA-256 `68a6bc19097ecc84a93583a39230b92b58b4a3ab8a2c0971ab50d084923bbb95` and `docs/builder-policy-evaluation-auxiliary.md`. The pinned source is `source/upstream/tex/chapters/generative_model_model_based.tex`, SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`, lines 413–455 (`eqn:superV-true`, `eqn:superV-hat`, `eq:Vl-inf-norm-bound`) and 457–480 for the subsequent error/variance event.

## Definitions and orientations

The source fixes a true model and policy, writes `P=P_π`, `P̂=P̂_π(data)`, `R=(I−γP)⁻¹` and `R̂=(I−γP̂)⁻¹`, and defines

```text
r⁰=r_π,  V⁰=Rr⁰=V^π,
r^(l+1)=sqrt(Var_P(V^l)),  V^(l+1)=Rr^(l+1),
V̂^l=R̂r^l.
```

The staged `auxiliaryValue` uses the actual infinite-trajectory `M.trajectoryExpectedValue π` at level 0 and the **true** inverse matrix and true policy-row population variance at successors. `auxiliaryReward` uses the actual policy-averaged source reward at level 0 and the same true successor variance at each later level. The independent `auxiliaryValue_zero_eq_inverse` proves that this source-semantic base equals `Rr⁰`, rather than replacing the actual value with a stipulated inverse. `auxiliaryValue_eq_inverse` covers all levels.

`empiricalAuxiliaryValue` applies the inverse of the **actual direct policy-evaluation empirical matrix** to `auxiliaryReward M π l`, which is the true model's same reward vector at that level. It does not substitute an empirical variance, recompute the true reward using the sample, or evaluate the true value with the empirical kernel. The proof identities `auxiliaryValue_matrix_equation` and `empiricalAuxiliaryValue_matrix_equation` multiply on the left by the corresponding `I−γP` or `I−γP̂` and obtain that common reward. The matrix is indexed current state by next state, and `mulVec` is row-by-column as in the source; the inverse and multiplication order are correct. Both invertibilities are separately proved in imported modules. `empiricalAuxiliaryValue_zero` identifies level zero with the actual plug-in `valueEstimator`, whose own prior review connects it to empirical trajectory value.

A compiled independent probe additionally checked by definitional equality that level one is precisely `R sqrt(Var_P(V^π))`, the fixed vector used in the separate empirical-resolvent comparison. The vectors at levels l≥1 can depend on the unknown true model, so they are analytical auxiliary objects, not claimed observable algorithm outputs. Their definitions omit sample data, but the code does not yet prove their simultaneous Bernstein event or its independence as a random-family theorem.

## Validity, nonnegativity, and growth

`DiscountedMDP` supplies finite nonempty carriers, stochastic transition rows, bounded nonnegative reward, and `0≤γ<1`. π is any fixed stationary randomized policy. No stronger action, support or discount condition is added. The auxiliary rewards at l≥1 need not lie in `[0,1]`; they are real vectors used in the finite matrix equations, not rewards placed into an MDP with an invalid bound. `auxiliaryReward_nonneg` proves base reward nonnegative by stochastic averaging and later rewards nonnegative by the real square root. `auxiliaryValue_nonneg` uses the actual Bellman equation, a finite-state minimizer and `γ<1`; it does not assume inverse entries positive or introduce that conclusion as a premise. This covers zero variance and γ=0.

`auxiliaryValue_norm_le_reward` proves `‖V^l‖∞≤‖r^l‖∞/(1−γ)` by the stochastic-row Bellman contraction. `auxiliaryReward_succ_norm_le` proves `‖r^(l+1)‖∞≤‖V^l‖∞` using `Var_P(V)≤P(V²)≤‖V‖∞²`, without nonzero-variance assumptions. Induction then gives the stated conservative estimate

```text
‖V^l‖∞ ≤ (1/(1−γ))^l ‖V^π‖∞.
```

The exponents, base case and direction check out. This is a valid generic bound and includes γ=0. It is not the source's sharper recursive factor `(sqrt 2/[γ sqrt(1−γ)])^l`; in the small-horizon limit γ→1 it is insufficient to claim the sharp source rate. Conversely, no blanket pointwise comparison between the two numerical factors for every γ is needed for its correctness. The source factor divides by γ, so its γ=0 endpoint requires separate interpretation; the present bound does not make that division.

## Remaining source dependencies

The definitions, actual plug-in link and nonnegativity enable the source's auxiliary construction, but do not establish the sharp variance-resolvent bound for every l, finite-family joint Bernstein event, the recursive empirical/true error estimate, unrolling with the source constants, terminal bound, or the high-probability sample-complexity theorem. In particular, the reviewed first-level true variance-resolvent result concerns `V^π`; using an analogous bound at higher l requires a separately justified theorem for the nonnegative auxiliary vectors and their potentially unbounded rewards. The source's intended proof may obtain this via scaling or a generalization, but it is not supplied here.

## Independent verification and identities

A temporary exact copy of the staged source, with the level-one definitional probe and ten appended `#print axioms` commands, compiled against the integrated true-resolvent and empirical-inverse imports via `bash scripts/lean-local.sh`. It completed without diagnostics. `auxiliaryValue_zero_eq_inverse`, `auxiliaryValue_eq_inverse`, `auxiliaryValue_matrix_equation`, `empiricalAuxiliaryValue_matrix_equation`, `empiricalAuxiliaryValue_zero`, `auxiliaryReward_nonneg`, `auxiliaryValue_norm_le_reward`, `auxiliaryReward_succ_norm_le`, `auxiliaryValue_nonneg`, and `auxiliaryValue_norm_growth` all use only `propext`, `Classical.choice`, and `Quot.sound`. No Lean source was modified by this review. This is a staged-source check; integrated source and production exports need the usual separate check.

## Integrated export recheck

`Formalization/Generative/PolicyEvaluationAuxiliary.lean` is byte-identical to the staged source at SHA-256 `68a6bc19097ecc84a93583a39230b92b58b4a3ab8a2c0971ab50d084923bbb95`. The integrated source compiled cleanly to its previously absent project-owned `.olean` using `bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/Generative/PolicyEvaluationAuxiliary.olean Formalization/Generative/PolicyEvaluationAuxiliary.lean`. A separate import-only probe through the integrated auxiliary-Bernstein module checked all ten exports listed above: each again depends only on `propext`, `Classical.choice`, and `Quot.sound`. This validates the actual integrated declarations but does not alter the source-scope limitations above; whole-project validation remains separate.

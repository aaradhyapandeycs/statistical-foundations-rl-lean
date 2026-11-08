# CHECK: Theorem 3.2 approximate-planner plan (independent plan check, critic stance)

Public copy of the independent plan check; local paths removed. The plan checked here is the builder's private plan; it is not published.

Date: 2026-11-08. Read-only check. No Lean or lake was run. Nothing under `Formalization/` was touched.

- Plan checked: the builder's private plan,
  sha256 `fa984e6370a1079982946209bd62e467fb6c30018db8e56d81fdce2dd3f0e3e7`. This matches the hash in the brief.
- Source: `source/upstream/tex/chapters/generative_model_model_based.tex` (MB),
  sha256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. This matches the plan.

I read the source first: MB:835–1030 (planning step, Algorithm, Theorem 3.2, the :943 paragraph, the "first attempt" decomposition). After that I read the plan, then the library code.

## Verdict: **GO WITH FIXES**

The mathematics of (A) is correct. The constant 10240 survives; I recomputed the margin below. The inventory of exact-optimality uses is complete up to two places where the same uses recur syntactically. Both are listed in fix 3. The fixes below concern statement hygiene, citations and specification gaps. None is a mathematical blocker.

## 1. Reading of claims (A) and (B) at MB:943

- MB:943 is one prose paragraph containing two claims.
  - (A) Theorem 3.2's guarantee holds for a deterministic π̂ with ‖V̂⋆ − V̂^π̂‖∞ ≤ 1/(N(1−γ)), "after increasing c₀".
  - (B) Empirical VI and PI reach that accuracy in O((1−γ)⁻¹ log(N/(1−γ))) iterations.

  The plan reads both correctly.
- V̂⋆ is the empirical *optimal* value. MB:1005 defines it as V̂⋆ := V̂^{π̂⋆}, with π̂⋆ an optimal policy of M̂. `valueEstimator` is the empirical trajectory value of `optimalGreedyAction`, and `policyEstimator_empirical_optimal` (ModelBasedPolicyLearning.lean:81) shows it dominates every stationary policy. The reading is right (plan Q2: yes).
- "The same sample complexity guarantee" means the guarantee of Theorem 3.2, which includes both eq. `V-epsilon-pertubed` and eq. `Q-epsilon-pertubed`. The V→Q step (MB:977–985) does not use optimality. Include the Q clause (plan Q3: yes).
- **(A) deserves its own Ch3 entry.** The rule in AGENTS.md is "every source result that COVERAGE records as proved". (A) is a substantive stated guarantee, a strengthening of Thm 3.2, so recording it as proved triggers the entry rule. `Thm3_2_approxPlanner_positiveN` is an acceptable name.
- **(B) is a separate claim.** It is deterministic planning, so give it a separate COVERAGE row. Plan Q1 asks whether it also gets an entry: yes, if it is recorded as proved. See §4 for the form.

## 2. Formal statement draft

- **Self-contained.** It has the same binders, the same `0<δ<1`, `0<ε≤1/(1−γ)`, the same budget expression and log argument, and the same `1 − δ ≤ …real` as `Thm3_2_positiveN` (Ch3.lean:41–60). Good.
- **∀ f inside the event is the right reading, and it is the stronger one.** The source asks for the guarantee of "a deterministic policy π̂ satisfying" the slack. A uniform event implies the guarantee for any data-dependent planner output.
  - This holds even for non-measurable selectors, because the event is fixed before f is chosen.
  - It is true because the underlying good event (A ∩ allRows) is planner-free, and the slack is then a deterministic, pointwise premise.
  - This is not hypothesis smuggling: the slack is the printed premise, and it sits inside the event per f.
- **Implies the current entry with the same c₀.**
  - From `EmpiricallyOptimal f`, `empiricallyOptimal_value_eq` gives a norm of 0, and 0 ≤ 1/(N(1−γ)) because N>0 and γ<1. So the new event is contained in the old event.
  - The plan says this holds "up to the value of c₀". It actually holds with the same witness.
- **Cast/norm.** `‖·‖` on `State → ℝ` is the sup norm, which equals ‖·‖∞. `1 / (N * (1 - M.discount))` elaborates with ↑N : ℝ. Fine.
- Defect: see fix 1, which concerns unqualified names.

## 3. Mathematics

### Uses of exact optimality

The plan names U1 and U2. I grepped every use of `EmpiricallyOptimal` and `empiricallyOptimal`. The files are AnyOptimalPolicy, JointEvaluation, SourcePointwise, MainSample, Statements/Ch3, and Ch3Definitions.

- **U1.** `empiricallyOptimal_performance` (AnyOptimalPolicy.lean:29–59), via `hf M.optimalGreedyPolicy s`. This corresponds to source MB:1015–1026: eq. `Vhat-Vstar-pistar-tot` at :1025 and the argmax justification at :1026. The plan cites :1018–1020, which is wrong (fix 2).
- **U2.** `all_empiricallyOptimal_evaluation_source_bound` (:75–105), via `empiricallyOptimal_value_eq`.
- **U2′ (same mathematical fact, separate syntactic site).** `joint_policyEvaluation_event` (JointEvaluation.lean, around :186–191) rewrites B's bound on ‖V̂⋆ − V^f‖ into ‖V̂^f − V^f‖ using `empiricallyOptimal_value_eq`. Under the approximate planner this rewrite is false. The new B′ must therefore be stated directly on ‖V̂^f − V^f‖.
- **U1′.** The singleton branch `singletonState_empirical_optimal_exact` (MainSample.lean:23–49, used at :92–106) calls U1. The plan replaces this branch with the S·A split.
- **Lemma 3.6 / `Lemma3_6_holds`.** It uses EO only to rewrite Vs = V̂^π. The plan bypasses it via `empiricalPolicyValue_source_error_bound`, which needs only β ≥ 0. Legitimate.
- **No third mathematical use.**
  - `trueOptimalPolicy_beta_event` is planner-free.
  - `empiricalOptimalValue_allRows_residual` (EmpiricalOptimalResidual.lean:50) is stated for V̂⋆ on all rows, for every (x,a), and is policy-free.
  - Measurability goes through `Set.to_countable` and is unaffected.

### η-perturbation of the row residual

Write D = V̂^f − V̂⋆.

- **Sign of D.** D ∈ [−η, 0] pointwise. The upper bound 0 comes from `policyEstimator_empirical_optimal`; the lower bound −η comes from the norm premise.
- **Mean term.** |(P̂−P)D| ≤ η using the sign, or ≤ 2η using only |D| ≤ η. Either works.
- **Variance term.** Both vectors lie in [0, 1/h] by `trajectoryExpectedValue_bounds` (Formalization/MDP/InfiniteReturn.lean:154–157). The empirical model has the same reward and γ. This resolves risk R1, which costs 0 lines.
  - `abs_variance_sub_le_of_Icc` with C = 1/h gives |Var_P V̂⋆ − Var_P V̂^f| ≤ 2η/h. This is correct but loose; the sharp covariance bound is ≤ η/(2h)+η². Loose is fine here.
  - √ subadditivity then gives √Var V̂⋆ ≤ √Var V̂^f + √(2η/h).
- **Absorption into β′ = 2β.** Constants verified:
  - √(β/N)·√(2η/h) ≤ √(β/N)·√(2/(Nh²)) = √(2β)/(Nh) ≤ β/(Nh). This needs β ≥ 2, and β ≥ 4 holds via `leaveOneOutBeta_ge_four`.
  - 2η ≤ 2/(Nh) ≤ β/(2Nh).
  - Total: √(β/N)√Var_f + (2 + 1 + 0.5)β/(Nh) = … + 3.5β/(Nh) ≤ √(2β/N)√Var_f + 4β/(Nh). This is the `hrow` of `empiricalPolicyValue_source_error_bound` (VarianceResolventBridge.lean:300) with β′ = 2β. ✓
  - Note: `hrow` is stated with `Var_{M.policyTransition π s}(H.trajectoryExpectedValue π)`, the true-row variance of V̂^f. That matches the transferred quantity. ✓

### Final radius

Notation: x = q² = β/(Nh³). The budget gives hcut: 720β ≤ Nh, so x h² ≤ 1/720.

| Term | Bound |
|---|---|
| r₀ | ≤ 27q (`sourceEvaluation_radius_le`); exactly √720·q ≈ 26.833q |
| r₁′ | = 2√(4x) + 12xh = 4q + 12xh |
| 12xh | (xh)² = x·(xh²) ≤ x/720, so 12xh ≤ 12q/√720 ≈ 0.4472q |
| η | ≤ 1/(Nh) = xh²/β ≤ xh²/4; (xh²)² ≤ x·xh² ≤ x/720, so η ≤ q/(4√720) ≈ 0.0093q |

- **Sum:** 27 + 4 + 0.4472 + 0.0093 = **31.4565q < 32q ≤ ε**. With the exact r₀ the sum is 31.29q. The margin is about 0.54q. The `herr` side (`mainSample_scalar_bounds`) is unchanged.
- **c₀ = 10240 works.** If the scalar proof is awkward, a fallback is c₀ = 20480. Then `herr` becomes 32√2·q ≈ 45q ≤ ε, which gives about 13q of room.
- **Caveat:** the existing `sourceEvaluation_radius_le` uses only x h² ≤ 1/16. That gives 12xh ≤ 3q, and the total becomes 34.0q > 32q. The new scalar lemma must use the 1/720 bound from hcut (fix 5).

### Case split

The plan's S·A ≤ 1 versus S·A ≥ 2 split replaces the one-state case. It is sound.

- **S·A ≥ 2.** K = SAN ≥ 2 is the only input `mainSample_log_comparison` needs. Neither `source_policyLearning_evaluation_with_pointwise` nor the joint event uses S ≥ 2; I checked that `hS` feeds only `hK` (MainSample.lean:107–116). One state with A ≥ 2 therefore goes through the general branch. ✓
- **S·A = 1.** Action is a subsingleton, so f = `policyEstimator` (and = `M.optimalGreedyAction`), and EO holds. The conclusion is then trivial for every data, or follows from `mainSample_policyLearning`. ✓
- **Rejected alternative.** One could keep the one-state route: V̂^f = V^f exactly, by `singletonState_empirical_policy_value_exact`, which does not need EO. That route needs η ≤ ε, i.e. c₀·L ≥ 1. This can fail at S=A=1 because L = log(1/(h²εδ)) can be close to 0. Keep the plan's split.

## 4. (B): VI/PI iteration counts

- **PI.** The argument is correct. The Lemma 2.1 PI clause (Ch2.lean:117–125) gives ‖Q^{π_k} − Q̂⋆‖ ≤ γ^k·‖Q^{π_0} − Q̂⋆‖ ≤ γ^k/(1−γ). Then `greedyImprove_policyFixedPoint_ge` (PolicyIteration.lean:68) and `policyFixedPoint_le_of_greedy_backup` (:148) give V^{π_{k+1}}(s) ≥ max_a Q^{π_k}(s,a) ≥ V̂⋆(s) − γ^k/(1−γ). So γ^k ≤ 1/N suffices: k ≥ log N/(1−γ) via log γ ≤ γ−1 for γ>0, and γ=0 is a separate case.
- **VI.** Greedy loss ≤ 2γ^k/(1−γ)² is correct. So γ^k ≤ (1−γ)/(2N), i.e. k ≥ log(2N/(1−γ))/(1−γ).
  - The non-robust greedy-loss lemma is indeed absent: no performance-difference or greedy-loss theorem was found in MDP/ or Generative/.
  - `RobustRL/DRVI/Planning.lean:116` `greedy_residual_bounds` gives only the one-step residual V⋆(s) − Q⋆(s,f s) ≤ 2γ^T/(1−γ). The missing step from that residual to the value loss (≤ ξ/(1−γ)) is a short contraction argument, about 50–100 lines.
- **Specification gaps (fix 7).**
  - The source does not specify the VI initialization or the VI output policy. State Q₀ = 0 (or any Q₀ with ‖Q₀ − Q̂⋆‖ ≤ 1/(1−γ)) and output = any greedy selector of Q_k.
  - For PI, allow any initial stationary π₀ and arbitrary greedy ties.
  - Explicit counts in the export are fine. For the Ch3 entry, the faithful form of O(·) is an existential universal constant C with k ≥ C·(1−γ)⁻¹·log(N/(1−γ)) (with a ⌈·⌉ or max(1,·) guard). The explicit-count lemma implies it.
  - Edge cases. log(N/(1−γ)) = 0 only at N=1, γ=0, and there every policy already satisfies the slack, because values lie in [0,1/(1−γ)] and the slack equals 1/(1−γ). So the O-form is not falsified at the boundary. Prove that case separately.
- **Bridge.** The policyFixedPoint/qOptimality iterates on `empiricalModel` must be identified with `trajectoryExpectedValue` / `valueEstimator`. The bridges cited in the Lemma 2.1 docstring exist. Budget +50–100 lines.

## 5. Size and risks

- **Size.** (A) is about 400–800 lines; the plan's 0.6–1.05k is conservative. (B) is about 250–450 lines. Combined, within TRIAGE M.
- **R1** is resolved; see fix 6.
- **R3.** The scalar step is real but has 0.54q of slack. It can be done via squared bounds: (12xh)² ≤ 0.2x and (4√720·η)² ≤ x. That avoids √720 decimals in nlinarith.
- **R6.** Agreed: add only parallel theorems, and keep `EmpiricallyOptimal`, `Thm3_2_positiveN` and `mainSample_policyLearning` untouched.
- **New risk R7.** Copying `joint_policyEvaluation_event` would also copy the U2′ rewrite. B′ must be a fresh set over `slack f → ‖V̂^f − V^f‖ ≤ r₁′`. The union-bound boilerplate can be reused.

## Required fixes

1. **Qualify names in the statement draft.** Use `StatisticalRL.ModelBasedPolicyLearning.samplingLaw`, `.valueEstimator` and `.empiricalModel`, as `Thm3_2_positiveN` does. Ch3.lean opens only `StatisticalRL.DiscountedMDP`. The Ch3 file must import definition modules only; all the names used live in `Ch3Definitions`. ✓
2. **Citations.**
   - The exact-optimality step is MB:1015–1026 (eq. `Vhat-Vstar-pistar-tot` at :1025, argmax at :1026), not :1018–1020.
   - The V→Q step is MB:977–985.
   - The docstring should cite `Thm:sample-compl-main` MB:900–923 and the prose claim MB:943, and say that the entry is a prose claim, not a numbered result.
3. **List U2′ and U1′ as optimality uses that the new chain must not inherit.** U2′ is the rewrite in `joint_policyEvaluation_event` around :186–191. U1′ is `singletonState_empirical_optimal_exact` / the MainSample singleton branch. Build B′ directly on V̂^f.
4. **Mean term.** Either prove the sign D ≤ 0 via `policyEstimator_empirical_optimal` (giving η), or use 2η. The plan's "≤ η (2η suffices)" is fine; just make the choice explicit. Both fit: 3.25 or 3.5 ≤ 4.
5. **Scalar lemma.** It must use x h² ≤ 1/720 (from hcut). Reusing `sourceEvaluation_radius_le`'s 1/16 premise for the 12xh term gives 34q > 32q. Reuse it only for r₀ ≤ 27q, or use the exact √720·q.
6. **R1 is resolved.** Cite `trajectoryExpectedValue_bounds`, Formalization/MDP/InfiniteReturn.lean:154–157, for both V̂⋆ and V̂^f on `empiricalModel`.
7. **(B) specification.**
   - Fix the VI init (Q₀=0 or ‖Q₀−Q̂⋆‖ ≤ 1/(1−γ)), the VI output (any greedy selector), and the PI start and ties.
   - Handle γ = 0 and N = 1.
   - Add the greedy-loss lemma (residual ξ to value loss ξ/(1−γ)) and the fixed-point/trajectory bridge.
   - The Ch3 entry should use an existential universal C (O-form). Explicit counts go in the library export.
8. **Ledgers.** Extend the SOURCE-ISSUES scope bullet (lines 456–459) to name `Thm3_2_approxPlanner_positiveN`. No new source issue is needed, because (A) is true as printed. COVERAGE gets separate rows for (A) and (B). Update TRIAGE 3.j. If 3.x (dropping N>0) lands first, add an un-suffixed entry then. Do not block on it.

## Answers to the plan's open questions

- **Q1.** Yes, (B) gets its own entry if it is recorded as proved, e.g. `Thm3_2_planningIterations`. Use an O-form with an existential constant and the specification of fix 7. Explicit counts belong in the library theorem. If (B) is deferred, COVERAGE must say open; do not fold it into (A)'s row as proved.
- **Q2.** Yes. V̂⋆ is the empirical optimal value (MB:1005); `valueEstimator` equals it.
- **Q3.** Yes, include the Q clause (MB:977–985 is optimality-free).
- **Q4.** U1 and U2 are the only mathematical uses. U1′ and U2′ are syntactic re-uses (fix 3). Lemma 3.6 uses EO only to rewrite Vs = V̂^π; bypassing it via `empiricalPolicyValue_source_error_bound` is not smuggling, because `hrow` is derived deterministically from the unchanged allRows event plus the in-event slack.
- **Q5.** Keep `_positiveN` now, consistent with the existing entry and disclosure. Fold it into 3.x later.

sha256 of checked plan: `fa984e6370a1079982946209bd62e467fb6c30018db8e56d81fdce2dd3f0e3e7`

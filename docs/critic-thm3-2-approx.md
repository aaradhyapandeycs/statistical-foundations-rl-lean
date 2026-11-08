# CRITIC: Theorem 3.2 approximate-planner extension (MB:943, claims A and B)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review covered the builder's pre-integration snapshot. The four library modules were integrated unchanged except for their imports (`PlanningEmpirical` now imports `Formalization.Generative.ModelBasedPolicyLearning` instead of `Statements.Ch3Definitions`, for import layering), as `Formalization/Generative/PolicyLearningApproxPlanner.lean` (ApproxPlanner), `Formalization/Generative/PolicyLearningApproxPlannerMain.lean` (ApproxPlannerMain), `Formalization/MDP/PlanningIterationCount.lean` (PlanningIterationCount) and `Formalization/Generative/PlanningEmpirical.lean` (PlanningEmpirical). The statement files became the entries `Thm3_2_approxPlanner_positiveN` and `Thm3_2_planningIterations` in `Formalization/Statements/Ch3.lean`, with their proofs in `Formalization/Statements/Ch3Proofs.lean`; on integration the entry docstrings were changed to address F1/F2 and to give a full `.tex` citation. The sanity probe `StatementImplies` was not integrated. Short module names below refer to these integrated files; the file hashes quoted below are those of the reviewed snapshot. The review text below is otherwise unchanged.

Date: 2026-11-08. Independent critic (did not build). No builder file, nothing under `Formalization/`,
and no `.lake/build/lib/lean/Formalization*` artifact was touched. No paper fetching, no lake, no LSP.

## Inputs and hashes

- Source `source/upstream/tex/chapters/generative_model_model_based.tex` sha256
  `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d` (matches plan/check). Read first:
  MB:900–923 (`Thm:sample-compl-main`), MB:943 (prose claims A, B), MB:1003–1026 (V̂⋆ definition,
  `Vhat-Vstar-pistar-tot`), and prelim.tex:312–345 (VI is Q-iteration `Q_k = T(Q_{k-1})` from an
  unspecified `Q₀`; PI is `π_k(s) = argmax Q^{π_{k-1}}(s,·)` from an unspecified `π₀`).
- The builder's reviewed snapshot (9 files): all 9 hashes equal
  the builder's snapshot hash list; the builder's live working files are byte-identical (`cmp`) to the snapshot.
  - ApproxPlanner 9d9cb97d…6b6a, ApproxPlannerMain 1e22e4de…2b2f, PlanningEmpirical 2611c513…6a7,
    PlanningIterationCount 36959224…a7, Statement f799c2a9…a7, StatementImplies ff41ce67…b9a8,
    StatementPlanning 88f941ed…eb6, StatementPlanningProof 29019b89…a49, StatementProof b1e15172…093.
- Critic copies: reviewer copies in the reviewer's private probe folder = snapshot with only the module prefix
  (builder's working prefix → reviewer's private prefix) replaced (diff-verified). Probe
  `CriticProbe.lean` (reviewer's private probe folder) sha256 `b32d477d91dd5014a3fbac070f3c1d2e345fae2ef507a29b41b93dc19f0bd0bc`.

## Independent compilation (critic-run)

`bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean <file>`, foreground, one at a
time, in order Statement, StatementPlanning, ApproxPlanner, ApproxPlannerMain, StatementProof,
StatementImplies, PlanningIterationCount, PlanningEmpirical, StatementPlanningProof: **all exit 0, empty
output (no warnings, no sorry)**, 1–5 s each. `CriticProbe.lean` (no olean): exit 0.

Axioms (critic probe output, kept in the reviewer's private probe folder), each exactly `[propext, Classical.choice, Quot.sound]`:
`mainSample_policyLearning_approx_universal_constant`, `mainSample_policyLearning_approx`,
`Thm3_2_approxPlanner_positiveN_holds`, `Thm3_2_approxPlanner_positiveN_imp`,
`Thm3_2_planningIterations_holds`, `empirical_planningIterations`, `greedy_value_loss`,
`valueIteration_value_loss_le`, `policyIteration_value_loss_le`, plus critic probes
`vi_planner_guarantee`, `pi_sequence_exists`.
Forbidden-token grep over snapshot (`sorry|admit|axiom |native_decide|implemented_by|unsafe|opaque|extern|set_option`): no hits.
Name-collision grep of all 25 new declaration names against `Formalization/`: none.

## 1. Statement fidelity

### `Thm3_2_approxPlanner_positiveN` vs MB:943 (A)

- Binders, `0<δ<1`, `0<ε≤1/(1−γ)`, budget `c₀·log(SAN/((1−γ)²εδ))/((1−γ)³ε²) ≤ N`, `1−δ ≤ μ.real`, V clause
  and Q clause (`γε`): token-identical to `Thm3_2_positiveN` (Ch3.lean:41–60), except the premise. ✓
- V̂⋆ = `valueEstimator` = empirical trajectory value of `policyEstimator = (empiricalModel …).optimalGreedyAction`;
  `policyEstimator_empirical_optimal` makes it dominate every stationary policy, matching MB:1005
  (`V̂⋆ := V̂^{π̂⋆}`, π̂⋆ optimal in M̂). ✓
- Norm: `‖·‖` on `State → ℝ` is the Pi sup norm = ‖·‖∞ over states (used via `norm_le_pi_norm`). ✓
  Slack `1 / (N * (1 - M.discount))` with `↑N : ℝ`. ✓
- Conclusion is about TRUE values `M.trajectoryExpectedValue/Q` of `pointMass ∘ f`, versus
  `M.optimalGreedyPolicy` (V⋆). ✓ `f : State → Action` = deterministic policy, as printed. ✓
- `∀ f` inside the event: covers any data-dependent (even non-measurable) planner output. Confirmed by critic
  probe `vi_planner_guarantee` (A + B ⇒ guarantee for an arbitrary data-indexed greedy-VI output `F data`). ✓
- "after increasing c₀": rendered as `∃ c₀`; the export actually keeps c₀ = 10240 (stronger). ✓
- Implies `Thm3_2_positiveN` with the same witness: `StatementImplies` recompiled by the critic. ✓
- The draft has no local `MeasurableSpace` instances (Ch3.lean has them). Harmless: `.real` takes the
  instance from `samplingLaw`'s type, and the `_imp` probe, which mixes both files, compiles.

### `Thm3_2_planningIterations` vs MB:943 (B)

- O-form: `∃ C > 0` before State/Action/M/N/data, `C/(1−γ)·log(N/(1−γ)) ≤ k`. This is the standard and faithful
  reading of "within O((1−γ)⁻¹ log(N/(1−γ))) iterations". Witness C = 4. ✓
- VI: `Q_k = (empiricalModel).qOptimality^[k] Q₀`, which is prelim.tex:316 on M̂. The output is any greedy selector `f` of Q_k. The conclusion
  is the printed slack `‖V̂⋆ − V̂^f‖ ≤ 1/(N(1−γ))`. ✓
- PI: arbitrary `π 0` (even stochastic, more general than the source). `π (n+1) = pointMass ∘ g n` with `g n` any
  argmax of `policyFixedPoint (π n)` (= Q^{π n}, via `trajectoryExpectedQ_eq_policyFixedPoint`). Guarantee for `π k`, k ≥ 1.
  This is prelim.tex:324–329 with arbitrary ties. ✓
- Non-vacuity: critic probes `greedy_exists` (greedy selectors exist for every Q) and `pi_sequence_exists`
  (a PI sequence from any π₀ satisfying both hypotheses exists) compile. `Q₀ = 0` satisfies the VI range
  premise (used in `vi_planner_guarantee`). The hypotheses are satisfiable; the statement is not vacuous. ✓
- N = 1: the slack equals the horizon 1/(1−γ), and every policy meets it (values in [0, 1/(1−γ)]). This holds for
  all γ, not only at the log-zero point γ = 0. The trivial branch is mathematically honest: the printed claim is
  itself trivial there. ✓
- Explicit counts were checked by hand. The VI count needs log2 + L ≤ 4L, which follows from L ≥ log 2 > 0. The PI count needs 3L ≥ 1 + log 2, and L ≥ log 2 gives
  3L ≥ 2.08. Both are Lean-checked. ✓
- Added `0 < N`: the printed claim divides by N, so N > 0 is implicit in the source. See F1 for the naming question.

## 2. No smuggled hypotheses

- No use of `empiricallyOptimal_value_eq` or the singleton-state branch in library modules. The only grep hits are
  `StatementImplies.lean:24` (non-library probe, legitimate there) and `ApproxPlannerMain.lean:113`
  `policyEstimator_empiricallyOptimal`. The latter is a proved library fact about the specific policy `policyEstimator`, not a premise.
- Subsingleton case `card S · card A ≤ 1`: card S ≥ 1 forces card A ≤ 1, so `Subsingleton Action` and every
  `f = policyEstimator`. That policy is empirically optimal, so the old `mainSample_policyLearning` event applies. Correct.
  The case `card S·card A ≥ 2` gives K = SAN ≥ 2, the only input to `mainSample_log_comparison`. ✓
- B′ (`all_approxPlanner_evaluation_source_bound`) is stated on ‖V̂^f − V^f‖. Its probability comes from the
  policy-free `empiricalOptimalValue_allRows_residual`, and the slack is a pointwise premise inside the event.
  Fix 3 is honoured.
- Row transfer: the mean term costs η, using the sign V̂^f ≤ V̂⋆. The variance term uses `variance_le_variance_add_of_Icc`
  with the [0, 1/(1−γ)] ranges, then √ subadditivity, then absorption `√(β/N)√(2η/h) ≤ β/(Nh)` (needs β ≥ 2; have β ≥ 4).
  Total √(β/N)√Var + 2β/(Nh) + β/(Nh) + η ≤ √(2β/N)√Var + 4β/(Nh), which is `hrow` with β′ = 2β. ✓
- Scalar check, recomputed: 12xh ≤ 12q/√720 ≈ 0.447q ≤ q/2; xh² ≤ q/√720 ≤ q/26; η ≤ xh²/β ≤ q/104.
  27 + 4 + 0.5 + 0.0096 = 31.51 ≤ 32 ✓. `herr` (32q ≤ ε) from the unchanged `mainSample_scalar_bounds`; c₀ = 10240 ✓.
- Q clause: `trajectoryQ_loss_le_discount_of_value_loss` (optimality-free, MB:977–985). ✓

## 3. Axioms

All re-probed by the critic. Every export listed above, and the critic probes, use only propext, Classical.choice and Quot.sound.

## 4. Library quality and placement

- Proposed placement is sound. `Generative/PolicyLearningApproxPlanner(.Main).lean`, `MDP/PlanningIterationCount.lean`
  (imports only MDP modules) and `Generative/PolicyLearningPlanningIterations.lean` [integrated as `Generative/PlanningEmpirical.lean`; see the post-review note] (imports Ch3Definitions,
  following existing Generative precedent, e.g. FiniteHorizonGenerativeSampling) are all fine.
- `greedy_value_loss` is a reusable, general MDP lemma (Singh–Yee 2ξ/(1−γ)). Names follow the local conventions.
- `StatementImplies` is a sanity probe. Keep it out of `Formalization/` (or at most in a non-index probe); it must
  not become a statement entry.

## 5. STATUS.md ledger drafts

These are accurate. Export names, c₀ = 10240 with strict `<`, C = 4, the explicit-count theorem names and the SOURCE-ISSUES
scope bullet all check out. The bullet starts at line 455, with body lines 456–459. TRIAGE 3.j is at line 82 of the private Ch2–4 triage ledger.
The COVERAGE (B) row should state the VI-initialization range explicitly (see D1).

## Verdicts

- `Thm3_2_approxPlanner_positiveN` (+ `mainSample_policyLearning_approx[_universal_constant]`): **ACCEPT WITH
  DISCLOSURES**. The only disclosure is the existing `N > 0` restriction, shared with `Thm3_2_positiveN`. Otherwise the
  entry states the printed claim, and the export is stronger (same c₀, strict `<`).
- `Thm3_2_planningIterations` (+ `empirical_planningIterations`, VI/PI explicit counts): **ACCEPT WITH DISCLOSURES**
  (D1–D3).

## R-items (blocking)

None.

## Disclosures (to carry into COVERAGE / docstrings)

- D1. The VI initialization is restricted to Q₀ with entries in [0, 1/(1−γ)]; the source leaves Q₀ unspecified. Some
  restriction is necessary: for an arbitrary Q₀ the count depends on ‖Q₀ − Q̂⋆‖, so no universal O-bound can hold.
  The docstring states this; COVERAGE should too.
- D2. PI guarantee is for `π k` with k ≥ 1, i.e. after at least one improvement. `π 0` is arbitrary.
- D3. `0 < N` (implicit in the printed claim, which divides by N).

## F-items (non-blocking)

- F1. Naming/doc consistency. The (B) docstring says "explicitly positive, as for `Thm3_2_positiveN`" but the entry
  has no `_positiveN` suffix and no SOURCE-ISSUES link. Either add the scope-disclosure link (STATUS already plans to
  name it in the bullet), or reword to "N > 0 is implicit in the printed claim (it divides by N)". Unsuffixed is
  defensible.
- F2. Optional: add `vi_planner_guarantee`-style composition (A ∘ B) as a documented remark. It is not needed for either entry.
- F3. On integration, recompile Ch3/Ch3Proofs/Formalization/Audit, and check that the two entries elaborate identically
  under Ch3.lean's local `MeasurableSpace` instances. The probe suggests they will.

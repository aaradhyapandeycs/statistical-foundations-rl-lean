# CRITIC: small batch 1 (independent, refutation stance)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review covered the builder's pre-integration snapshot. The six entries were integrated on 2026-11-08 with the R1/F1/F2/F3/F5 docstring fixes and imports-only changes: entries in `Formalization/Statements/Ch2.lean`, `Ch4.lean` and `Ch7.lean` with wrappers in the matching `Ch{2,4,7}Proofs.lean`; library modules `Formalization/MDP/RewardPerturbation.lean`, `Formalization/ModelFree/MeanError.lean`, `Formalization/ModelFree/AsyncQ/MeanError.lean`, `Formalization/RobustRL/DRVI/OraclePlanner.lean`, `OraclePlannerNumerics.lean` (snapshot OraclePlannerMain) and `OraclePlannerMain.lean` (snapshot OracleMain). Short module names below refer to the reviewed snapshot files, and the file hashes are those of the snapshot. The regret-to-PAC item (d) of the batch plan is not covered by this review. The review text below is otherwise unchanged.

Date 2026-11-08. Critic did not build these items; builder files were not edited; no paper fetching.
Status: COMPLETE.

## Inputs verified
- The builder's reviewed snapshot (12 files): all 12 sha256 match the builder's snapshot hash list;
  the builder's live working files are byte-identical to the snapshot (`cmp`). The builder's status file sha256 `890f8ef8…`
  equals the value recorded in the builder's build log.
- Source sha256 match the plan: prelim `2d27bb72…`, MF `7f4eb058…`, robust_RL `95ce19a9…`.
- Source read first: prelim.tex:613–653; MF:179–239 (Thm 4.1, Remark 4.1), :876–929 (Thm 4.6, Remark 4.2),
  :2054–2090 (rate, Thm 4.12, Remark 4.3; the commented remark at :2093ff is not part of the text);
  robust_RL.tex:342–372 (Thm 7.2, Remark 7.1).

## Independent compilation (critic)
Snapshot copied to the reviewer's private probe folder with the module prefix (builder's working prefix → reviewer's private prefix) changed in imports only (entry
and library bodies byte-identical: Ch2Entries/RewardPerturbation/Ch4Entries/MeanError/Ch7Entries/OraclePlanner
hashes equal the snapshot). Each compiled with `bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean`,
foreground, one at a time (compile log kept in the reviewer's private probe folder). All 12 exit 0, no warnings, no errors
(a first pass failed only because the output directory did not exist; rerun after `mkdir`).
Grep of all 12 files: no `sorry`/`admit`/`axiom`/`native_decide`/`maxHeartbeats`/`opaque`/`unsafe`.

## Axioms (critic probe `Probe.lean` in the reviewer's private probe folder, exit 0, output `probe.out`)
All six wrappers (`Eq_QV_pi_perturbation_r_inf_holds`, `Eq_QV_star_perturbation_r_inf_holds`,
`Ch4.Remark4_1_holds`, `Ch4.Remark4_2_holds`, `Ch4.Remark4_3_corrected_holds`,
`Ch7.Remark7_1_restricted_holds`) and the library exports `optimal_reward_perturbation`,
`tv_oracle_planner_guarantee`, `asyncQ_meanError_exists_constants`: `[propext, Classical.choice, Quot.sound]`.
Agrees with the builder's `axiom-probe.out`.

## Structural checks
- G2: `Ch2Entries` imports only `MDP.FixedPointDefinitions`, `MDP.CoreDefinitions`; both are already lines 2–3 of
  `scripts/gates/g2_statement_imports.txt`. No new edge. Ch4Entries/Ch7Entries import lists are identical
  (`diff`) to the working-tree `Statements/Ch4.lean` / `Ch7.lean`.
- Entry files contain only `def … : Prop` (no `theorem`, no `by`). Wrappers are one-line terms applying a single
  library export (Ch2: tuple of two exports; no restatement or re-proof).
- No name clash: none of the six names occurs in `Formalization/Statements/*.lean` or `docs/COVERAGE.md`.
- Deviation 2 (copied proofs): `gap_le_of_residual`/`tv_good_gap_of_valueGap` (OraclePlanner) and
  `tv_selfBoundExpr_le_of_planning` (OraclePlannerMain) are generalized copies of `gap_le`/`tv_good_gap`/
  `tv_selfBoundExpr_le`, as the plan (§c, lines 331–335) prescribed so that frozen modules stay untouched.
  Acceptable; duplication is tech debt only (F5).
- Deviation 5 (heartbeat workaround): no `set_option maxHeartbeats`/`maxRecDepth` appears anywhere in the 12
  files, so there is nothing to accept or reject. Note: the builder's status file has no numbered deviations 1–6; its "Notes and
  deviations" has three bullets. If a later version of the status file numbers them, re-check against this snapshot.

## Per-entry findings

### `Eq_QV_pi_perturbation_r_inf` (prelim.tex:613–631) — ACCEPT
- Setting matches: same S, A, P, γ (premises `M'.transition = M.transition`, `M'.discount = M.discount`),
  rewards differ; ∀ π stationary randomized. Q^π = `policyFixedPoint` (Lemma2_1 convention), V^π(s) =
  E_{a∼π(s)} Q^π(s,a). Both printed bounds stated; sup norms are the finite Pi norms; `‖r − r̃‖` is the
  sup norm on S×A. `DiscountedMDP` enforces γ ∈ [0,1) and r ∈ [0,1] (book convention prelim:42), so
  `/(1−γ)` is never junk. Omitting the printed resolvent equalities (proof steps) is disclosed.
- Library proof (Bellman self-bound D ≤ d + γD) read in full; sound.

### `Eq_QV_star_perturbation_r_inf` (prelim.tex:633–653) — ACCEPT (docstring nit F1)
- ⨆ encoding of max_π: first conjunct proves `(s,a) ↦ ⨆ π Q^π(s,a) = optimalityFixedPoint` for both models
  (`iSup_policyFixedPoint_eq_optimalityFixedPoint`: `ciSup_le` with `policyFixedPoint_le_optimal`, and
  `le_ciSup_of_le` at `optimalGreedyPolicy` with explicit bound 1/(1−γ)), so the Q-suprema are genuinely
  attained, not the ℝ junk value; Q⋆ is tied to Lemma2_1's Q⋆.
- Middle link `≤ ⨆ π ‖Q^π − Q̃^π‖`: bounded (each term ≤ ‖r−r̃‖/(1−γ)), proof uses `le_ciSup` with that bound.
- V⋆ part: `⨆ π E_{π(s)} Q^π(s,·)`; BddAbove proved (`bddAbove_policyValue`, ≤ 1/(1−γ)), and
  `Nonempty (StationaryPolicy)` from `optimalGreedyPolicy`; so not a junk ⨆. Printed V⋆ = max_π V^π matches.
- Empty-type junk: excluded by `state_nonempty`/`action_nonempty` fields.

### `Remark4_1` (MF:226–239) — ACCEPT
- Statement = `Thm4_1` with δ := ε(1−γ)/2 substituted: same ∃c₁ c₂ c₃ order and side conditions
  (0<c₂≤c₁, 0<c₃), same rate window 1 ≤ t ≤ T with log²T, same V₀ range, budget
  `c₃ log³T · log(2ST/(ε(1−γ))) / ((1−γ)³ε²) ≤ T` exactly as printed in the remark.
- Five-part conclusion: 0<δ, δ<1 (printed "δ ∈ (0,1)"), Integrable, E[max_s|V_T−V^π|] ≤ ε(1−δ)+δ/(1−γ), ≤ 2ε.
  `max_s` = `⨆ s` over a finite nonempty type of |·| (bounded, Finite range). Integrability is concluded, so the
  Bochner junk value 0 cannot make the bound vacuous. Expectation is under the same `tdSourceSamplingLaw` as Thm4_1.
- Same constants: the library reuses the very export `Thm4_1_holds` uses
  (`tdSource_policyEvaluation_exactSamples_accuracy_exists_universal_constants`), so the witnesses coincide
  (docstring states this; the Prop itself can only say ∃, as the plan check Q1 accepted).
- Crude bound uses `tdIterate_bounds_positive_rates` (rates on 1..T only); `tdIterate_bounds` untouched.

### `Remark4_2` (MF:914–929) — ACCEPT
- Statement = `Thm4_6` with δ := ε(1−γ)/2: same ∃ order, A ≥ 2, T ≥ 2, rate window k ≤ T with log³T, budget
  `c₃ log⁴T · log(2SAT/(ε(1−γ)))/((1−γ)⁴ε²) ≤ T` as printed in the remark. Q⋆ = trajectory Q of
  `optimalGreedyPolicy` as in Thm4_6. Five-part conclusion as in 4.1; library reuses
  `qLearning_exists_universal_constants_source_accuracy` (the export behind `Thm4_6_holds`).

### `Remark4_3_corrected` (MF:2088–2090; C34) — ACCEPT WITH DISCLOSURES (R1 docstring, C34 sentence)
- Reading: the remark has no formula; "As before" → mirrors 4.1/4.2 with δ = ε(1−γ)/2 inside Thm 4.12's budget
  (log²(SAT/δ) → log²(2SAT/(ε(1−γ)))), five-part conclusion, ∃c₁∈(0,1] ∃c₂ in Thm4_12_corrected's order; c₂
  enlarged (`max c₂⁰ 1`) is within "essentially the same sample complexity". Faithful.
- Premises are exactly Thm4_12_corrected's (diffed by eye: stationarity, uniform ergodicity, IsLeast t_mix,
  μ_min attained, 0<μ_min, 1≤T, `2 ≤ T ∨ 2 ≤ S·A`, 0<ε≤1), δ removed. Rate `c₁ log³T/((1−γ)Tμ_min)` same.
- T = 1 counterexample to the uncorrected reading re-derived: S=A=1, γ=1/2, r=1, Q₀=0, μ_min=1, t_mix=0,
  ε=1/2 (δ=1/8): budget LHS = c₂·log²8·max(0,0) = 0 ≤ 1, rate 0, Q₁ = Q₀ = 0, Q⋆ = 2, mean error 2 > 1 = 2ε.
  Correct. Critic machine-checked the pieces (Probe.lean): `async_iterate_rate_zero` (rate 0 ⇒ every
  `AsyncQ.iterate` equals Q₀), `rate_at_T1` (rate = 0 at T = 1), `budget_at_T1` (budget at this instance is
  ≤ 1 for every c₂). Q⋆ = 2 and the integral were not formalized.
- R1 (docstring only): add "This counterexample is a paper computation and is not formalized" (as
  `Thm4_12_corrected`'s docstring does for its own), optionally citing the critic probe pieces.

### `Remark7_1_restricted` (robust_RL.tex:361–372) — ACCEPT WITH DISCLOSURES (scope line)
- Õ reading `c_opt (1−γ)² log(SAN/((1−γ)δ)) / N`, order ∀ c_opt ≥ 0 ∃ C₂ > 0: matches the commented factor at
  :367 and the plan check. Log argument > 1 (S,A,N ≥ 1, (1−γ)δ < 1), so the tolerance is ≥ 0, not junk.
- Premises on γ, σ, δ, ε, N and the sample-size condition are verbatim those of `Thm7_2_corrected` (minus T and
  pick); conclusion is for the true RMDP M, V^{⋆,σ} the sup over stationary randomized policies
  (`robustOptimalValue` = sSup of range; attained/bounded via `robustOptimalValue_eq_optFix`).
- Event uniform over all deterministic f (stronger than a fixed selector; no measurability needed under the `⊤`
  σ-algebra). |·| requirement equivalent to one-sided as V̂⋆ ≥ V̂^f; library uses only `le_abs_self`.
- Non-vacuity (critic probe `r71_requirement_met`, compiled): on every data set the exact empirical robust-optimal
  deterministic policy `detPolicy (optPolicy (ballFamily tvBall M̂ σ) M̂)` has gap exactly 0, so the requirement
  is met by a real planner and the event is not vacuously satisfied.
- Numerics: `oracle_planning_bounds` (Ξ ≤ 1, Ξ/(1−γ) ≤ ε/2 from C₂ ≥ 2c_opt) and
  `tv_selfBoundExpr_le_of_planning` (statistical terms + planning ≤ ε) compile; conclusion not weakened;
  base constant 10⁶ unchanged.
- Restriction: deterministic stationary outputs only (randomized/history-dependent π̂ not covered) and N > 0
  (`hN`). Correctly `_restricted`.
- F2: the docstring's "reverse order is false" and "higher powers of the log … would fail as δ → 0" are paper
  arguments (plan check §3), not formalized; say so.

## R-items (required before integration)
- R1. `Remark4_3_corrected` docstring: mark the T = 1 counterexample as a paper computation, not formalized
  (pieces checked by the critic probe). Docstring-only; no signature change.

## F-items (recommended, non-blocking)
- F1. `Eq_QV_star_perturbation_r_inf` docstring says "all suprema here are attained"; the library proves
  attainment only for the Q-suprema (and boundedness for the V- and norm-suprema). Reword to "the Q-suprema are
  attained (first conjunct); the V- and norm-suprema are bounded above by 1/(1−γ) and ‖r−r̃‖/(1−γ)".
- F2. `Remark7_1_restricted` docstring: label the two order/power claims as paper arguments.
- F3. Remark 4.1/4.2 docstrings: optionally name the reused export (`…exactSamples_accuracy_exists_universal_constants`,
  `qLearning_exists_universal_constants_source_accuracy`) so "same constants" is traceable.
- F4. At integration rename the builder's working-prefix imports and recompile Statements files, `Formalization.lean`, `Audit.lean`;
  rerun the axiom probe on the integrated names.
- F5. Tech debt: the copied DRVI lemmas could later replace the originals (`gap_le`, `tv_good_gap`,
  `tv_selfBoundExpr_le` are special cases); do not do this inside the batch.
- F6. Remark 4.2/4.3 entries rely on the TD/Q crude bound being proved for the given rate windows; this is
  proved, nothing to do — noted only because rates outside the windows (η 0 for 4.1) are unconstrained.

## Ledger text (proposed)

COVERAGE rows:
- `| Reward-perturbation bounds, eq:QV-pi-perturbabtion-r-inf and eq:QV-star-perturbabtion-r-inf, preliminaries lines 613–653 | [MDP/RewardPerturbation.lean](../Formalization/MDP/RewardPerturbation.lean), [Ch2.lean](../Formalization/Statements/Ch2.lean), [Ch2Proofs.lean](../Formalization/Statements/Ch2Proofs.lean) | **Proved** (`Eq_QV_pi_perturbation_r_inf`, `Eq_QV_star_perturbation_r_inf`): for two discounted MDPs differing only in the reward, ‖Q^π−Q̃^π‖∞, ‖V^π−Ṽ^π‖∞, ‖Q⋆−Q̃⋆‖∞ and ‖V⋆−Ṽ⋆‖∞ are at most ‖r−r̃‖∞/(1−γ), with max_π read as the supremum over stationary randomized policies and shown equal to the optimal Bellman solution. The proof is a Bellman self-bound, not the printed resolvent route. Independently plan-checked and source-reviewed. |`
- `| Remarks 4.1 and 4.2 (mean estimation), model-free chapter lines 226–239 and 914–929 | [ModelFree/MeanError.lean](../Formalization/ModelFree/MeanError.lean), [Ch4.lean](../Formalization/Statements/Ch4.lean), [Ch4Proofs.lean](../Formalization/Statements/Ch4Proofs.lean) | **Proved** (`Remark4_1`, `Remark4_2`): with δ = ε(1−γ)/2 and the constants of Theorems 4.1/4.6, E[max|error|] ≤ ε(1−δ)+δ/(1−γ) ≤ 2ε under the printed budgets; integrability is part of the conclusion. Independently plan-checked and source-reviewed. |`
- `| Remark 4.3 (mean estimation, asynchronous Q-learning), model-free chapter lines 2088–2090 | [ModelFree/AsyncQ/MeanError.lean](../Formalization/ModelFree/AsyncQ/MeanError.lean), [Ch4.lean](../Formalization/Statements/Ch4.lean), [Ch4Proofs.lean](../Formalization/Statements/Ch4Proofs.lean) | **Corrected variant proved** (`Remark4_3_corrected`): the remark has no formula; read as Remarks 4.1/4.2 (δ = ε(1−γ)/2 in Theorem 4.12's budget, E[max|Q_T−Q⋆|] ≤ 2ε), under the premises of `Thm4_12_corrected` ([C34](SOURCE-ISSUES.md#C34)). Independently plan-checked and source-reviewed. |`
- `| Remark 7.1 (oracle planners, TV), robust chapter lines 361–372 | [DRVI/OraclePlanner.lean](../Formalization/RobustRL/DRVI/OraclePlanner.lean), [DRVI/OraclePlannerMain.lean](../Formalization/RobustRL/DRVI/OraclePlannerMain.lean), [Ch7.lean](../Formalization/Statements/Ch7.lean), [Ch7Proofs.lean](../Formalization/Statements/Ch7Proofs.lean) | **Restricted variant proved** (`Remark7_1_restricted`): reading Õ((1−γ)²/N) as c_opt(1−γ)²log(SAN/((1−γ)δ))/N, for every c_opt ≥ 0 some C₂ (max(10⁶, 2c_opt)) makes Theorem 7.2's guarantee hold, with probability ≥ 1−δ simultaneously for every deterministic planner output meeting the requirement; randomized outputs not covered ([scope](SOURCE-ISSUES.md#statement-index-scope-disclosures)). Independently plan-checked and source-reviewed. |`

C34 sentence (append):
"Remark 4.3 (`:2088–2090`, no displayed formula) is indexed as `Remark4_3_corrected`: read like Remarks 4.1/4.2
(δ = ε(1−γ)/2 in the budget, E[max|Q_T−Q⋆|] ≤ ε(1−δ)+δ/(1−γ) ≤ 2ε), it fails under the printed premises by the
same T = 1 instance (ε = 1/2: mean error 2 > 1) and is proved with exactly the premises of `Thm4_12_corrected`
(c₁ = 1, c₂ = max(c₂⁰, 1)); the counterexample is a paper computation."

Scope line (Statement-index scope disclosures):
"- Remark 7.1 (`remark:tv-upper`, `robust_RL.tex:361–372`) is indexed as `Remark7_1_restricted`: Õ((1−γ)²/N) is read
  as c_opt(1−γ)²log(SAN/((1−γ)δ))/N with ∀ c_opt ∃ C₂; only deterministic stationary planner outputs are covered
  (randomized or history-dependent outputs are not), and N > 0 is assumed as in `Thm7_2_corrected`. The event is
  uniform over all such outputs, so no measurability of the planner is needed."

## Verdict summary
| Entry | Verdict |
|---|---|
| `Eq_QV_pi_perturbation_r_inf` | ACCEPT |
| `Eq_QV_star_perturbation_r_inf` | ACCEPT (F1 docstring nit) |
| `Remark4_1` | ACCEPT |
| `Remark4_2` | ACCEPT |
| `Remark4_3_corrected` | ACCEPT WITH DISCLOSURES (R1, C34 sentence) |
| `Remark7_1_restricted` | ACCEPT WITH DISCLOSURES (scope line, F2) |

Critic artefacts: kept in the reviewer's private probe folder (reviewer copies, Probe.lean, probe.out, out-*.txt, compile-log.txt);
oleans only in the reviewer's private olean folder. Nothing under `Formalization/` or the project's `Formalization*` build outputs
was touched.

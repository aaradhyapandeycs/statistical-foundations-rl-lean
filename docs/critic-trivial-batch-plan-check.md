# CHECK: independent critic review of the trivial-batch plan

Public copy of the independent plan check; local paths removed. The plan checked here is the lead's private batch plan for three batches (B: Chapter 7, A: Chapter 6, C: Chapters 2–5); it is not published.

Post-review note (added to this public copy, 2026-11-08): batch C was then built and independently reviewed in `critic-trivial-c.md`, which reviewed the pre-integration snapshot, and integrated into the library on 2026-11-08. The C4-a item 3 docstring wording proposed below ("With S = 0 or A = 0 … vacuous at N = 0") was superseded by that critic's R1: `EnvironmentStage` carries nonempty state and action types and 0 < ε ≤ H forces H ≥ 1, so S, A, H ≥ 1 always hold, at N = 0 the printed threshold forces δ ≥ HSA ≥ 1, and the `Thm3_9` entry is never vacuous. Item numbers such as 4.j, 4.n, 3.p and D11–D20 refer to the lead's private work list, which is not published. Batches B and A were then built, independently reviewed in `critic-trivial-b.md` and `critic-trivial-a.md`, and integrated on 2026-11-08/09. Their critics found the same slip as this check's B2-a wording (corrected by batch B's R1: over all policies the DPO minimum 0 is attained at boundary policies, and it is over full-support policies that the infimum is unattained) and replaced A7's "corrected" framing by `Lemma6_2_iterationCount_restricted` (batch A's R1: open, not refuted, for γ < 1/2). The check text below is otherwise unchanged.

Date: 2026-11-08. Reviewer: independent plan checker (critic stance). Source-only review. No Lean or lake was
run, nothing under `Formalization/` was touched, and no paper was fetched. Lean names were checked by grep and by
reading the definitions. Nothing here certifies the final Lean code. Each landed entry still needs its own critic
pass against the compiled export.

## 0. Pins

- Plan: the lead's private batch plan (not published), sha256
  `4ecd6180d4537b479c9e194aeffdeaa6a7b8c502f74e503f0fb1e9e2e2f92b59` (verified, 906 lines; matches the brief).
- Source hashes: all nine chapter hashes in the plan's table match `shasum -a 256` of
  `source/upstream/tex/chapters/*.tex` (prelim 2d27…, MB b7e7…, MF 7f4e…, ON 3933…, OFF 67cf…, ROB 95ce…,
  marl 8fad…, FED c9df…, RLHF e601…).
- Numbering: the Remark/Example numbers in the plan agree with the generated `docs/NEXT.md` (Remarks 4.5, 5.5,
  6.2–6.5, 7.2) and with the environment order in `offlineRL.tex` (remarks at :45, :142, :175, :357, :413).

## 1. Verdicts

| Batch | Verdict | Blocking fixes |
|---|---|---|
| B (Ch7) | **GO WITH FIXES** | X1, X2, B1-a, B2-a, B4-a |
| A (Ch6) | **GO WITH FIXES** | X1, X2, A1-a, A7-a |
| C (Ch2–5) | **GO WITH FIXES** | X1, X2, C1-a, C4-a, C5-a, C7-a, C7-b |

No item is false as printed. Every Prop draft is true under its stated reading, re-derived below. The fixes
concern proof-route layering (X1), the ledger and disclosure bookkeeping (X2), two small c₃/positivity gaps
(C5, C7), one wrong case split (C4), and one reading that the Prop does not literally cover (C7, single action).

## 2. Cross-cutting fixes (all batches)

**X1 (blocking): library modules must not cite `*_holds` wrappers.** The plan's own §7 says new library modules
must not import `Formalization.Statements.*` (`g2_library_to_statements.txt` is frozen). Several proof routes,
however, cite wrappers that live in `Statements/ChNProofs.lean`. The builders must use the underlying library
exports instead (all names verified to exist):

| Plan cites | Lives in | Use instead (library) |
|---|---|---|
| `Lemma2_1_holds` (C1) | `Ch2Proofs.lean:44` | `DiscountedMDP.value_iteration_error`, `DiscountedMDP.arbitraryGreedyPolicyIteration_error` (`MDP/PolicyIteration`) |
| `Thm3_1_holds` (C3) | `Ch3Proofs.lean:22` | `ModelBasedPolicyEvaluation.policyEvaluation_universal_constant` |
| `Thm4_7_holds` (C5) | `Ch4Proofs.lean:110` | `qLb_thm47` |
| `Lemma4_15_holds` (C7) | `Ch4Proofs.lean:114` | `qLb_lemma415` |
| `Thm5_2_corrected_holds` (C9) | `Ch5Proofs.lean:158` | `onlineUCBVI_actual_regret_high_probability` (plus the `simpa` unfolding used there) |
| `Lemma6_2_corrected_holds` (A7) | `Ch6Proofs.lean:30` | `Input.lem_monotone_contraction_corrected` |

`Thm3_9_positiveN_holds` (C4) is fine, because C4 is a wrapper in `Ch3Proofs.lean` itself. Alternatively, a
two-line derivation may live directly in `ChNProofs.lean`. In that case drop the owned library file and say so in
PROGRESS.

**X2 (blocking): bookkeeping in the same change.** AGENTS.md requires the statement entry to land in the same
change that records the result as proved. The plan lists integration edits to `Statements/*`,
`Formalization.lean`, and (for C4 only) the ledger. It must also schedule the following:
- `docs/COVERAGE.md` and `docs/named-result-status.json` rows for every one of the 20 entries;
- `docs/SOURCE-ISSUES.md#statement-index-scope-disclosures` bullets for every new `_restricted` entry: B1 (extend
  the Remark 7.1 bullet to Remark 7.2), B2–B4 (finite `X, Y`, full-support `π_ref`, argmin over full-support
  policies; see F4 below), and C7 if fix C7-b takes the suffix route;
- `docs/PROGRESS.md` ownership rows for the three builders and three critics (plan §7 says "to record by the lead").
G3 resolves the anchors that exist today (`C8`, `C10`, `C18`, and the heading slug
`statement-index-scope-disclosures`). It does not check that the cited section actually discloses the new
restriction.

**X3 (advice): names-in-scope claim.** Plan §4 says "every name below is already used by an entry in the same
file". This is not literally true: `onlineCappedBackwardValueAt` and `onlineCappedBackwardQAt` are not used by an
existing Ch5 entry. They are, however, transitively imported through `CappedGreedyPlannerDefinitions`, whose
planner unfolds `onlineCappedBackwardQAt`. No allowlist change is needed. I checked every draft's identifiers
against the current imports of Ch2–Ch7, and none needs a new import. The G2 allowlist is untouched, as the plan
says.

## 3. Batch B (Ch7)

### B1 `Remark7_2_restricted` (ROB:453–457; Thm 7.4 :437–450). Status: GO WITH FIXES

- **Source re-read.** The remark extends Theorem 7.4 to "any oracle planning algorithm" whose output satisfies
  `‖V̂^{⋆,σ} − V̂^{π̂,σ}‖∞ ≤ O(log(SAN/((1−γ)δ))/N²)`. It is analogous to Remark 7.1.
- **Truth.** True under `∀ c_opt ≥ 0 ∃ c₂`. I re-derived it with ε(1−γ) ≤ 1 and
  N ≥ c₂L'/((1−γ)³ε²) ≥ c₂L'/(1−γ):
  - `c_opt L'/(N²(1−γ)) ≤ c_opt ε/(c₂N) ≤ ε/8` once `c₂ ≥ 8c_opt`;
  - `c_opt/(N²(1−γ)²) ≤ c_opt(1−γ)⁴ε⁴/(c₂²L'²) ≤ c_opt ε/(c₂² log²2) ≤ ε/8` once `c₂² log²2 ≥ 8c_opt`;
  - `L ≤ L' + log(1/(1−γ)) ≤ L' + 1/(1−γ)`.
  The SA = 1 split is legitimate: with one action, the empirical and true optimal values are attained by the only
  policy.
- **Quantifier order.** `∀ c_opt, 0 ≤ c_opt → ∃ c₂ > 0, ∀ State Action M σ δ ε N hN, …`. The premises are exactly
  those of `Thm7_4_corrected` (checked line by line against `Ch7.lean:468`). The event quantifies over all `f`
  inside, as in `Remark7_1_restricted`. Correct.
- **Suffix.** `_restricted` (deterministic stationary planner outputs) is needed and honest, and matches 7.1.
- **B1-a (blocking: correct the risk note).** The plan says Ξ enters `selfBoundExpr` "only linearly, through
  B·Ξ". This is wrong. In `GapBound.lean:25`, Ξ enters as `√(2B'(1+Ξ)/(γ²(1−γ)²))`, plus the separate additive
  term `Ξ/(1−γ)` in `chi_selfBoundExpr_le`. Consequences:
  1. The new numerics lemma must carry the hypothesis `Ξ ≤ 1` (the plan already has it; it gives 1+Ξ ≤ 2).
  2. The existing `hΞ : Ξ ≤ 2(1−γ)/N²` admits 1+Ξ up to 2.5, so the inner bound has room, and
     `selfBoundExpr_mono_Ξ` is available.
  3. The budget split must be re-done: `2·selfBound ≤ ε/2` and `Ξ/(1−γ) ≤ ε/2`, instead of the current joint
     `≤ ε`. The `c₂ = 10⁶` slack (`P ≤ 9ε²/10⁶` in the `Thm74Numerics` header) makes this plausible, but the
     builder must verify it rather than assume it. The stop rule (BLOCKER, never weaken) is correct.
- **Reuse names verified:** `gap_le_of_residual` (`OraclePlanner.lean:58`, parametric in `ball`),
  `residual_le_valueGap` (:34), `chi_good_gap` (`Thm74.lean:73`), `chi_selfBoundExpr_le` (`Thm74Numerics.lean:25`),
  `chi_L_lower` (:267, takes `2 ≤ S*A`), `oracle_planning_bounds` (`OraclePlannerNumerics.lean:123`),
  `thm7_4_corrected_holds` (`Thm74Main.lean:23`), `tv_oracle_planner_guarantee` (`OraclePlannerMain.lean:27`).
- **Size.** 300–550 is plausible.

### B2 `Eq_DPO_restricted` (RLHF:62–74, :90). Status: GO WITH FIXES

- **Truth.** All four clauses re-derived.
  - (i) β·(log π_r/π_ref(y₊) − log π_r/π_ref(y₋)) = r(y₊) − r(y₋), by `log_gibbs_div`. Uses β ≠ 0.
  - (ii) r := β log(π/π_ref) gives Z = Σπ = 1.
  - (iii) r − r' = β(log Z_r − log Z_{r'}) depends on x only. Needs π_ref > 0 and β ≠ 0, both premises.
  - (iv) The two-line argmin transfer is correct. No existence is claimed, which matters (see F4).
- **Quantifier order.** Clause (iv) correctly puts `∀ π, IsPositivePolicy π →` outside the iff. Correct.
- **B2-a (blocking: docstring and disclosure must give the real reason for the suffix).** The suffix is needed
  mainly because the argmin is taken over full-support policies, not because X, Y are finite. In the source's
  extended-real reading, a policy with `π(y₋|x) = 0` makes `−log σ(+∞) = 0`. So over all policies the DPO
  infimum can be 0 and unattained, while every full-support policy has positive loss (for example, a dataset
  whose only pair is (x, y₁, y₂)). In Lean, `log 0 = 0` would also make zero-mass policies take junk values.
  The book's derivation implicitly works with the Gibbs (full-support) policies. Say this explicitly in the
  docstring and in the scope-disclosure bullet. Also say that `π_ref > 0` is an implicit source premise (`log π_ref`
  appears in `eq:reward-policy-eq`).

### B3 `Eq_policy_RBMLE_restricted` (RLHF:115–141). Status: GO

- **Truth.** All clauses re-derived.
  - (i) `vpoObjective_gibbs` (needs row sums of π_cal = 1, from `IsCondPolicy`) and `optCalValue_eq` (needs ρ ≥ 0,
    β > 0).
  - (ii) As in B2.
  - (iii) Holds for π > 0 and π_cal ≥ 0, since `klDiv p q = Σ p log(p/q)` and the terms with π_cal = 0 vanish on
    both sides.
  - (iv) Holds for every π, with K = sign·αβ Σρ Σπ_cal(log π_cal − log π_ref).
- **Fidelity of the inline formula.** The inline DPO term in (iv) matches `vpoObjective`'s syntax
  (`β * log … - β * log …`, `RlhfPrinted712.lean:54`). Good.
- **Suffix.** As B2.

### B4 `Eq_online_RBMLE_restricted` (RLHF:158–198). Status: GO WITH FIXES

- **Truth.** (a) holds for every r (the minimality hypothesis is unused there), by `calValue_le_optClosed` and
  `calValue_gibbs`. (b) holds via B3 (ii) with sign = +1. Dropping uniqueness is correct.
- **B4-a (blocking, cheap).** `eq:RLHF-policy` (:172–175) maximizes the uncalibrated `J(r,π)` of `eq:KL_reward`
  (:41–45), not `calValue`. The plan only proposes to mention this in the docstring. Instead, state clause (a)
  with the printed J written inline: `∑ x, ρ x * (∑ y, π x y * r x y − β * klDiv (π x) (π_ref x))`. It differs
  from `calValue` by the π-independent `Σρ Σπ_cal r`, so the proof cost is one `ring`/`sub` step, and the entry
  then states the printed object.

## 4. Batch A (Ch6)

### A1 `Example6_1` (OFF:348–355, proof :361–379). Status: GO WITH FIXES

- **Source re-read.** The printed claim is `E[r⋆ − r_{a^emp}] ≥ 0.075` for N ≥ 2. The proof uses
  `P(r̄₂ ≥ 1) ≥ 0.15`.
- **Truth.** `P(Z ≥ 1) = 0.15866`, so the printed proof's 0.15 is correct and ½·0.1587 = 0.0793 ≥ 0.075. The
  exact value is `P(Z > √((N−1)/N))`: 0.2398 at N = 2, decreasing to 0.1587. The plan's "≈ 0.159" is the limit.
  I recomputed its midpoint sum: width ¼ on [1, 3.25] gives **0.15746**, not 0.1579 (immaterial).
- **Prop.** `∀ N ≥ 2, ∀ sel` returning an empirical best arm, with the lower Lebesgue integral. This is stronger
  than the printed claim (every tie rule, no measurability), and the integrand is nonnegative because `r 0 = 1`
  is r⋆. Correct and honest. Name `Example6_1` with no suffix is right.
- **A1-a (blocking simplification; removes a fragile step).** Use E := {Σ_{i<N−1} zᵢ ≤ 0} ∩ {z_{N−1} > 1}
  instead of `<` / `≥`. Then r̄₁ ≤ 1 < r̄₂, so `sel z = 1` still follows. Also P(Σ ≤ 0) ≥ ½ follows from symmetry
  alone (P(Σ≤0) = P(Σ≥0), and the two sum to at least 1). This removes plan step 3's need for P(Σ = 0) = 0 via
  `stdGaussianPi_abs_linear_le` and the δ ↓ 0 limit. The numeric lemma becomes `0.15 ≤ P(Z > 1)`, which is the
  same integral.
- **A1-b (advice on numerics).** A coarser grid suffices. Width ½ on [1, 3] (midpoints 1.25, 1.75, 2.25, 2.75)
  gives 0.15488 ≥ 0.15, with a 3% margin, and needs only four `exp` lower bounds plus `π < 3.15`. Width ⅓ on
  [1, 3] gives 0.15624. Convexity of φ on [1, ∞) holds (φ'' = (x²−1)φ). Prove the Hermite–Hadamard step by
  pairing `f(m+t) + f(m−t) ≥ 2f(m)`. The 300-line stop rule and "do not weaken 0.075" are right.

### A2 `Remark6_5` (OFF:413–415; penalty :400–402). Status: GO

- **Source.** `b_a = √(2 log(4A/δ)/N_a)`. With A = 2 this is `armRadius 2 δ n` = √(2 log(8/δ)/n). Verified
  against `BanditDefinitions.lean:37,41`: `lcbFallback` uses `Fintype.card Arm`.
- **Truth.** `fixedMask_gaussianMean_tail_pi` (`FixedMaskGaussianMean.lean:90`) bounds the bad event
  `{b < |mean noise|}` by δ/(2·|Act|) = δ/4 per arm, so δ/2 in total. On the good event: r₂^lcb ≤ 0;
  r₁^lcb ∈ [1−2b₁, 1]; and 1−2b₁ > 0 iff N−1 > 8 log(8/δ). Both counts are positive, so C18 is not reached.
  Correct.
- **Reading (F5).** Acceptable. No suffix needed.

### A3 `Remark6_4` (OFF:357–359). Status: GO

- **Truth.** b=0 gives 1/((N−1)/N) = N/(N−1); b=1 gives 0/(1/N) = 0. The limit is 1.
- **Reading (F5).** The example's design is deterministic, so the empirical frequency is the only available d^b.
  Acceptable. The docstring should name this as a reading.

### A4 `Eq_defn_Cstar_bandits` (OFF:264–281). Status: GO

- **Truth.** True in ℝ≥0∞ for any measure: 0/x = 0 including x = 0, and 1/x = x⁻¹. Trivial but faithful. The
  `Measure` encoding matches `Thm6_1_zeroCountFallback_corrected`.

### A5 `Remark6_2` (OFF:142–151). Status: GO (advice)

- **Truth.** Re-derived the contradiction argument. Where d⋆ > 0 and d^b = 0 the ratio is ∞, so every ratio < 1
  forces d⋆ < d^b on the support of d⋆. Summing gives 1 < 1.
- **Advice.** The proof works for every policy. Since the source's π⋆ is "the optimal deterministic policy"
  (ties possible), consider stating the Prop for every stationary policy π, or every optimal deterministic π.
  This avoids tying the entry to the `optimalGreedyPolicy` tie choice, and follows today's precedent of
  "Theorem 3.9 for any optimal policy". If the `Thm6_13` convention is kept instead, the docstring must say so.

### A6 `Remark6_3` (OFF:175–185). Status: GO (advice)

- **Truth.** (i) holds by `min_le_left` plus monotonicity. (ii) Discount 0 with ρ = δ_{s₀} and db = d⋆ gives
  d⋆ = δ_{(s₀, greedy(s₀))}, so the ratio is min{1, 1/S}/1 = 1/S, and the off-support terms are 0/0 = 0. Correct.
- **Advice.** "Can be as low as 1/S" is set against "C⋆ always ≥ 1", so the natural reading includes the lower
  bound `C⋆_clipped ≥ 1/S` (attained). The plan notes that this lower bound is true but leaves it out. It is
  cheap: d⋆ of a deterministic policy has at most S support points, so some point has d⋆ ≥ 1/S, and the ratio
  there is ≥ (1/S)/d^b ≥ 1/S. Recommend adding it as clause (iii). Same remark about ∀ π as A5 for clause (i).

### A7 `Lemma6_2_iterationCount_corrected` (OFF:892). Status: GO WITH FIXES

- **Truth.** γ^τ ≤ e^{−(1−γ)τ} ≤ ε(1−γ) gives `γ^τ/(1−γ) ≤ ε`. When ε(1−γ) > 1, τ = 0 works trivially. `γ < 1`
  is a field of `OfflineVILCB.Input` (`γ_lt_one`, `VILCBDefinitions.lean:25`), so no extra premise is needed,
  which answers the plan's open question.
- **Suffix.** `_corrected` (C10) is honest. At γ < ½ the fixed point need not be unique, so "approximation of
  Q̂⋆_pe" is ill-posed.
- **A7-a (blocking).** X1: use `Input.lem_monotone_contraction_corrected`, not `Lemma6_2_corrected_holds`.

## 5. Batch C (Ch2–5)

### C1 `Lemma2_1_iterationCount` (P:357–360). Status: GO WITH FIXES

- **Truth.** Holds for k ≥ 1 via `γ^k D ≤ ε` ⇐ `(1−γ)k ≥ log(D/ε)` (and γ^k = 0 when γ = 0). At k = 0, log ≤ 0
  forces D ≤ ε. The PI clause has the same binders as `Lemma2_1`. The quantifier order (ε outside the
  conjunction) is fine.
- **C1-a (blocking).** X1: use `value_iteration_error` and `arbitraryGreedyPolicyIteration_error`.
  `discount_pow_le_of_log_le` (`MDP/PlanningIterationCount.lean:178`) exists, and so does the layer-1 placement
  `MDP/IterationCount.lean`.

### C2 `Eq_Qpi_Vpi_matrix_notation_inf` (P:496–531). Status: GO

- **Truth.** True. The four displays match 2.24a–d. `P_π` and `P^π` match `Lemma2_3`. The source also writes the
  intermediate `Q^π = r + γP^πQ^π`. Optionally add it as a fifth conjunct; it is the step before (d) and costs
  nothing.

### C3 `Eq_Vhatpi_Vpi_difference_decoupled_Hoeffding` (MB:270–276). Status: GO (with X1)

- **Truth.** Re-derived. With ε := √(c·log(S/(δ(1−γ)))/((1−γ)³N)), the `Thm3_1` threshold holds with equality.
  Then log(1/(1−γ)) < 1/(1−γ) ≤ L/(log 2·(1−γ)) gives ε² ≤ c(1+1/log 2)·L/((1−γ)⁴N). When ε > 1/(1−γ), the crude
  bound applies. S = 1 is exact.
- **Missing case.** S = 0 is also quantified (`Fin 0`). It is trivial (the sup norm over an empty type is 0), but
  the builder should list it.
- **Proving through Thm 3.1.** The plan proves the display from Thm 3.1 rather than by the printed Hoeffding
  route. That is legitimate, because the entry states the result, not the route.

### C4 `Thm3_9` printed form (MB:2551–2570). Status: GO WITH FIXES

(C4 here is the plan item, not SOURCE-ISSUES C4. SOURCE-ISSUES C4, two-state testing strictness, is unrelated.)

- **Honesty.** The upgrade is honest. The source says "for any δ > 0", and `Thm3_9_positiveN` already has only
  `0 < δ`. The `∀ hN : 0 < N` form inside the event coincides with `Thm3_9_positiveN` at N > 0. At N = 0, the
  printed hypothesis (well-defined, since the log has no N) forces log(HSA/δ) ≤ 0, so δ ≥ HSA ≥ 1, where the
  conclusion is trivial. This differs genuinely from Thm 3.2 and Lemma 3.5 (see F2). I agree the entry can be
  named `Thm3_9`, and the ledger move is the lead's call after critic review.
- **C4-a (blocking: the wrapper's case split is wrong, and so is one sentence of the docstring).**
  1. The plan says that δ < 1 with N = 0 "contradicts the threshold since log(HSA/δ) > 0". This fails when
     `Fintype.card State = 0` or `Fintype.card Action = 0`. Then HSA = 0, Lean's `log 0 = 0`, and the threshold
     `0 ≤ 0` is met at N = 0 for every δ.
  2. Fix: at N = 0, do not argue from the threshold. The event `{data | ∀ hN : 0 < 0, …}` is `univ`, and
     `samplingLaw_probability` (`Generative/FiniteHorizonGenerativeSampling.lean:21`) gives measure 1 ≥ 1 − δ.
     This handles every δ.
  3. Docstring: write "the threshold forces N > 0 whenever δ < 1 and S, A ≥ 1. With S = 0 or A = 0 the printed
     log is undefined and the Lean statement is vacuous at N = 0." (The phrase "measureReal ≤ 1 gives the bound"
     for δ ≥ 1 has the wrong direction. The bound is `1 − δ ≤ 0 ≤ μ.real`.)

### C5 `Thm4_7_iterationLowerBound` (MF:992–1000). Status: GO WITH FIXES

- **Truth.** Contrapositive of `Thm4_7`. The quantifier order (M chosen before ε) matches the export.
- **C5-a (blocking).** The plan says "c₃ = 16 forces T ≥ 16, so log T > 0". But `Thm4_7`'s c₃ is existential;
  the Prop does not expose 16. If the export's c₃ < 1/16, then T could be 1, `log T = 0`, `c_lb/0 = 0`, and the
  rearrangement fails. Fix: choose the new entry's witness `c₃' := max c₃ 1`. Then T ≥ 16·c₃' ≥ 16 because
  (1−γ)⁻² ≥ 16, and raising c₃ only shrinks the regime. Alternatively, unfold `qLb_thm47`'s concrete constant.
  Also apply X1 (`qLb_thm47`).

### C6 `Thm4_6_constantRate` (MF:945–953). Status: GO

- **Truth.** c₂k ≤ c₁T for k ≤ T, and log T > 0 for T ≥ 2. Then η ≤ log³T/(c₁(1−γ)T), and the threshold gives
  the bound `(1−γ)³ε²/(c₁c₃ log T · log(SAT/δ))`. `log(SAT/δ) > 0` holds since SAT ≥ 2 and δ < 1. True.
- **Content.** The first clause is mostly tautological (η is the lower envelope), which is fine. The value lies in
  the upper-envelope and Õ clauses.

### C7 `Remark4_5` (MF:3455–3457). Status: GO WITH FIXES

- **C7-a (blocking).** Same c₃ issue as C5. `Lemma4_15`'s `c₃` is existential, and positivity of
  `c/(√((1−γ)²T)·log T)` needs T ≥ 2. Use the witness `c₃' := max c₃ 1` (with `qLb_lemma415`, per X1).
- **C7-b (blocking: fidelity of the single-action half, flag F6).**
  1. The source says "when there is only a single action a, E[ξ_max] = E[ξ(a)] = 0". The first clause instead
     proves `E ξ_t(a) = 0` for each a in the **two-action** hard instance, where `qLbAuxValue` is the max over both
     actions.
  2. The single-action model has a different V̂ (V̂ = Q̂(a)), so the clause is the mechanism behind the remark,
     not the printed statement.
  3. Either (i) generalize: prove mean zero for any V̂-process adapted to the first k−1 samples. `qLb_integral_xi`
     only uses independence of P_k from V̂_{k−1}; check whether its proof is generic. Then instantiate with a
     single-action auxiliary iterate. Or (ii) name the entry `Remark4_5_restricted`, with a scope-disclosure
     bullet stating that the single-action claim is represented by per-action mean zero on the two-action
     instance. Do not ship it unsuffixed with only a docstring caveat.
- **Positivity reading.** Reading "strictly positive" on t ≥ τ̂ is acceptable (the remark sits inside the Lemma
  4.15 context, and ξ = 0 at t = 0).
- **Names verified.** `qLb_integral_xi` (`QLearningLowerBoundAuxMoments.lean:300`) takes only `hrow`, `t ≤ N`
  and `a`, with η free as a section variable. `qLbMDP_rowSpec` takes `1/4 < γ`, matching `(by linarith)` from
  `3/4 ≤ γ` as in `Lemma4_15`.

### C8 `Remark5_5_corrected` (ON:790–802). Status: GO

- **Truth.** True by unfolding. `List.drop h` of `List.ofFn` gives `stage h :: rest`. `onlineCappedBackwardValue`
  is `actionMaximum (onlineCappedStageQ …)` and `onlineCappedBackwardQ` is the same `onlineCappedStageQ` with the
  same continuation (`CappedPlanningDefinitions.lean:49–70`). The planner chooses a with `Q a = sup'`
  (`CappedGreedyPlannerDefinitions.lean:19`). The `Nonempty` instances differ only by proof, so they agree.
- **Scope.** The Prop covers every stage h (the source states h = 1). It is stronger, which is fine.
- **F7.** See §7.

### C9 `Eq_regret_asymptotic_ucbvi_corrected` (ON:491–506). Status: GO (with X1)

- **Truth.** K ≥ S³AH³ ⇔ S⁴A²H⁶ ≤ SAH³K ⇔ S²AH³ ≤ √(SAH³K). So 20(√· + S²AH³)(1+I) ≤ 40√(SAH³K)(1+I). The C8
  inheritance is correct.
- **Placement.** Put the new premise before `∃ c₁ c₂`, in terms of `Fintype.card`. (`S` and `A` are `let`-bound
  only inside.)

## 6. Reuse spot-check (10+ names, all found with the claimed meaning)

`gap_le_of_residual`, `residual_le_valueGap`, `chi_good_gap`, `chi_selfBoundExpr_le` (Ξ hypothesis as described in
B1-a), `chi_L_lower`, `oracle_planning_bounds`, `fixedMask_gaussianMean_tail_pi` (bound δ/(2|Act|) as claimed),
`stdGaussianPi_abs_linear_le`, `log_gibbs_div` (`log(π_r/π_ref) = r/β − log Z`), `gibbsPolicy_isPositive`,
`partitionFn_pos`, `optCalValue_eq` (sSup = closed form, needs ρ ≥ 0), `vpoObjective_gibbs` (needs π_cal row sums
1), `calValue_le_optClosed`, `calValue_gibbs`, `discountedJointOccupancy_sum`, `discountedJointOccupancy_discount_zero`,
`optimalGreedy_discountedJointOccupancy_indicator`, `discount_pow_le_of_log_le`, `qLb_integral_xi`,
`qLbMDP_rowSpec`, `empiricalResolvent_isUnit`, `trajectoryExpectedValue_bounds`,
`policyEvaluation_universal_constant`, `trajectoryExpectedQ_eq_policyFixedPoint`. No owned new file path collides
with an existing file. All paths fit `docs/LAYOUT.md` §1, including layer 1 for the `MDP/` files.

## 7. Views on the flags

- **F1 (17 Õ read-offs as "implied by X" without entries).** I agree that no Prop entries are needed, because Õ
  has no fixed formal meaning and the template's inversion lemmas are real work. Four conditions apply:
  1. The COVERAGE status must be a distinct, non-proved category, for example "Õ read-off, informal; follows from
     <entry>; not machine-checked". It must never count toward proved totals, since the implication itself is
     unverified (thresholds with log N need an inversion argument).
  2. Rows whose parent is `_corrected`/`_restricted` (4.u→C34, D12→C32, D19→C45, D20→C41, D16/D18→C37) must say
     "inherits Cxx". "Implied by" an amended theorem does not imply the printed Õ claim.
  3. Comparison rows (3.p, 4.e, 4.j-gap, 4.y, D16) must cite both the upper-bound and lower-bound entries and the
     lower bound's regime (for example, `Thm3_7_corrected` needs S ≥ 16 for A = 1).
  4. Row 4.n's first display line is an explicit proof-step inequality, not a read-off. Label it "proof step,
     not formalized".
- **F2 (positiveN faithful for Thm 3.2 and Lemma 3.5).** I agree. Their printed thresholds contain log(SAN/·),
  which is undefined at N = 0, so the source's own domain is N ≥ 1. A `∀ hN` entry would hold at N = 0 only
  because of Lean's `log 0 = 0` making the threshold `0 ≤ 0` plus a vacuous event. That is junk-driven, so no
  such entries should be added. Rewording the scope disclosure is right. Reclassify the ledger status to
  "printed (N ≥ 1 implicit)" but keep the entry names. Whoever does the reclassification should record that
  this critic concurred. This is consistent with C4: Thm 3.9's threshold is N-free, so there the N = 0 case is a
  genuine, defined instance.
- **F3 (D11 Bernstein LCB-Q).** I agree it is not formalizable as stated. The display (OFF:1779–1789) has no
  citation, the Bernstein-penalty LCB-Q is never defined, "for sufficiently small ε" is unquantified, and
  Thm 6.8's `(1−γ)⁻⁵` does not imply `(1−γ)⁻⁴`. Record it as an open obligation (NFAS: algorithm undefined), not
  as dropped. Formalizing it under the prove-cited rule would mean the project designing the algorithm and its
  constants, which needs a user decision.
- **F4.** Keep `_restricted` for B2–B4. The main reason is the full-support argmin domain (B2-a), not
  finiteness.
- **F5.** The A2 and A3 readings are acceptable as drafted.
- **F6.** The t ≥ τ̂ reading is fine. The single-action reading is not covered literally (C7-b).
- **F7.** Keep `_corrected` for C8. The Lean tables are the C8-completed UCBVI object (`onlineZeroCountSafeQUpdate`).
  A bonus-free generic version would be a tautology about arbitrary tables, so it adds nothing.

## 8. Sizes

The estimates are plausible. B1 risk is medium (B1-a). A1 drops by about 40–80 lines with A1-a and A1-b. C4 is
smaller with the `univ` argument. C7 grows by about 60–120 lines if C7-b route (i) is taken.

## 9. Recommended order

1. **C4 first** (30–60 lines; it settles the Thm 3.9 status question and gets critic review early). Then the
   rest of batch C, which is all small and serves as a warm-up for the reviewers.
2. **B in parallel with C**, on the second compiler slot. Start with B2–B4 (pure algebra, low risk), then B1.
3. **A when a compiler slot frees.** Start with A4, A5, A3 and A7 (small), then A2, then A1 (numerics, with the
   A1-a/A1-b simplifications). At most two Lean compilers at any time, so the three builders take turns.

The lead integrates `Formalization.lean` serially and applies X2 in each batch's landing change.

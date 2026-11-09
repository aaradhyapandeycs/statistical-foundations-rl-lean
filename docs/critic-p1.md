# CRITIC — batch P1 (Ch1–2 prelim displays, KL ≤ χ²)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-09): this critic reviewed the pre-integration drafts. They were integrated on 2026-11-09 as follows: `DRAFT-STATEMENT.lean` → the ten new entries in `Formalization/Statements/Ch2.lean`; `DRAFT-Ch2Proofs.lean` → the wrappers in `Formalization/Statements/Ch2Proofs.lean`; `DRAFT-Ch1.lean` → `Formalization/Statements/Ch1.lean`; `DRAFT-Ch1Proofs.lean` → `Formalization/Statements/Ch1Proofs.lean`. R1–R5 and advisories A1–A3 were applied before landing. R3 and A1–A3 are docstring-only, so the `KLChiSquared.lean` hash differs from the one quoted below. Labels such as U1–U9 and #1–#9 number the rows of the builder's draft coverage text; F-P1-n and "CHECK" refer to the independent completion check. Where the text below quotes the rejected draft wording (R1), the token it quotes was removed from `COVERAGE.md`. The review text below is otherwise unchanged.

Critic: independent (not the builder). Date 2026-11-09.
Brief: the completion plan, batch P1, as amended by the independent completion check (findings F-P1-1..7).

## Overall verdict: **ACCEPT WITH FIXES**

All 11 entries state the printed result faithfully (some state more). The proofs are wrappers.
The axioms are clean. Required fixes R1–R5 are docstring, ledger and PR text only. No Lean signature changes.

## Evidence (critic's own runs)

- Source hashes: prelim.tex `2d27bb720d49…a5` and intro.tex `6bfa41c0bcb9…`, matching the drafts.
- File hashes match BUILD-LOG: KLChiSquared `430df244…`, PrelimDisplays `a2c3f3e1…`, DRAFT-STATEMENT `64296e70…`,
  DRAFT-Ch2Proofs `0dcb0b75…`, DRAFT-Ch1 `e2e31c08…`, DRAFT-Ch1Proofs `6b2abffe…`.
- `bash scripts/lean-local.sh`, one process at a time, with `pgrep -x lean` < 2 every time:
  - `Formalization/Probability/KLChiSquared.lean` exit 0
  - `Formalization/MDP/PrelimDisplays.lean` exit 0
  - `DRAFT-STATEMENT.lean` standalone exit 0, so the definition-only imports suffice
  - `DRAFT-Ch1.lean` standalone exit 0, with Mathlib imports only
  - the critic probe file exit 0 (64 s). It imports `Formalization` plus all new modules and drafts, and output is in
    the critic probe output. All 11 `_holds` and the new library theorems (`two_mul_sq_tv_le_klDiv_le_chiSquared`,
    `finite_det_optimal_eq`, `greedyDetSeq_dominates`, `trajectoryExpectedQ_eq_optimalityFixedPoint_of_optimal`,
    `qOptimality_eq_ciSup`) depend only on `[propext, Classical.choice, Quot.sound]`. The probe adds no name collisions.
  - The probe also checks `klDiv (dirac true) (dirac false) = ⊤` (see Eq_KL_ub_chi2).
- A grep for `sorry|admit|axiom|native_decide` over the new library files and drafts finds nothing.

## Per-entry verdicts

| Entry | Source | Verdict | Notes |
|---|---|---|---|
| `Eq_defn_Vpi_inf` | prelim 94–106 | ACCEPT, docstring fix R2 | `trajectoryExpectedValue` is defined as `∫ infiniteDiscountedReturn ∂infiniteTrajectoryLaw` (InfiniteReturn.lean:43), and the path's `trajectoryState`/`(path t).1` are s_t/a_t. Integrability and `0 ≤ V ≤ 1/(1−γ)` hold for every stationary randomized π, which is the policy class of :66. Omitting the T_π fixed point (F-P1-7) is disclosed, and it is in `Eq_bellman_consistency_V`. |
| `Eq_defn_Qpi_inf_horizon` | 117–121, 126–129 | ACCEPT | The forced-first-action law `stepMeasure (pointMass a)` matches :123 ("first taking action a … then following π"). The bounds are extra and disclosed. The identity V = E_{a∼π}Q is printed. |
| `Eq_optimal_Vstar_Qstar_defn` | 132–143 | ACCEPT | ∃ deterministic f with joint V and Q domination over all stationary randomized π, at every (s,a). Q⋆ and V⋆ do not depend on which optimal f is used. Competitors are stationary because "policy" is defined as stationary at :66 (see also :76). This matches CHECK U1, and no `_restricted` is needed. No library tie choice appears. |
| `Eq_defn_dpi_occupancy_discounted_dist` | 145–160, 163–174 | ACCEPT (advisory A3) | The printed formulas are inline, with the event probabilities under the actual path law mixed over ρ. `tsum` junk is harmless because the sum = 1 conclusions force summability. The indicator identity holds for **every** deterministic f, which is stronger than for π⋆ alone. |
| `Eq_bellman_consistency_V` | 191–223 (+ P_π :70–74) | ACCEPT | T^π, T_π and P_π are written inline. Q^π is a fixed point and the unique one (:209), and V^π = T_π V^π. |
| `Eq_bellman_fix_point` | 233–246 | ACCEPT | The entry covers **every** optimal deterministic f under the joint-domination hypothesis, the same notion as U1. `⨆ a'` equals max because Action is finite and nonempty (`DiscountedMDP.action_nonempty`). Fixed point and uniqueness are both stated. The hypothesis is satisfiable (builder probe-tail plus `exists_stationary_trajectory_optimal`). |
| `Eq_gamma_contraction_preliminary_inf` | 251–261 | ACCEPT | ‖·‖ on `State → Action → ℝ` is the nested Pi sup norm, max_{s,a}\|Q(s,a)\|, which is the printed ℓ∞. It holds for every π and all Q₁, Q₂. |
| `Eq_dh_pi_defn` | 749–774 | ACCEPT | d_h is the final-state event of `trajectoryLaw (take i)`, mixed over ρ. d_h(s,a) samples one more stage, and `next.1` is the stage-i action. Three conjuncts: the product form, d_1 = ρ, and the indicator for **every** deterministic Markov policy (F-P1-3 met). h ∈ [H] corresponds to `Fin stages.length`. |
| `Eq_Bellman_finite_pi` | 784–794 | ACCEPT | `trajectoryValue`/`trajectoryQ` are actual path-law expectations (TrajectoryDefinitions:46, ActionTrajectoryDefinitions:22), not recursions. The terminal value is 0, and both equations hold for every h ∈ [H] and every nonstationary randomized Markov policy. |
| `Eq_Bellman_finite_opt` | 798–806, 738–746 | ACCEPT (advisory A2) | IsOptimal means joint V and Q domination over all randomized Markov policies at all (s,a,n<H). The entry asserts existence and the optimality equations for **every** optimal deterministic f, with no `optimalValueAt`/`greedyActionAt` in the Prop (F-P1-3 met). `[Nonempty Action]` is justified by the printed 𝒜 = {1,…,A} (prelim :36). Each `EnvironmentStage` already carries `action_nonempty`, so the binder matters only for H = 0. |
| `Eq_KL_ub_chi2` (Ch1) | intro 216–247 | ACCEPT (advisory A1) | TV = sup over measurable A of \|P(A)−Q(A)\| (the `⨆` over a bounded nonempty family, so it is genuine). Mathlib `klDiv` equals the printed ∫log(dP/dQ)dP when P ≪ Q (+∞ iff not integrable, and the negative part is always integrable). χ² as `∫⁻ ofReal((dP/dQ−1)²) dQ` is the printed integral of a nonnegative function. **P ≪ Q is the printed scope (:229)** and is *necessary* for this χ² formula. For P = δ_true and Q = δ_false, KL = ⊤ (checked in the probe), while the lintegral using the Lebesgue-decomposition `rnDeriv` (= 0 Q-a.e.) is 1. So KL ≤ "χ²" would be false without the hypothesis. The Pinsker half holds without ≪ (`two_mul_sq_tv_le_klDiv`). |

Proofs: every `_holds` applies library exports. The extra glue is short and only derives the printed form: `le_antisymm` for Q⋆/V⋆ uniqueness, `controlled_getElem`/`drop_length` rewrites in finite_opt, and `convert` to the occupancy event lemmas. Nothing is re-proved. The new mathematics, (i) mutual domination, (ii) `finite_det_optimal_eq`, (iii) the d⋆ indicator and (iv)/(v) KL/χ²/Pinsker, is in the library files as required.

## Required fixes

- **R1 (G3 failure + wrong cross-reference).** the draft docs U6 row ends with "Correction C1." The G3 `CID_RE` reads this as a SOURCE-ISSUES id, and `docs/SOURCE-ISSUES.md` has no `id="C1"` anchor (count 0). Its "Candidate C1" is the unrelated Theorem 3.7(i) singleton-actions issue. Replace the text with
  "Category correction 1 of the completion check (definition, not a result)." and do not use the token `C1`.
- **R2 (Eq_defn_Vpi_inf docstring).** Replace "`chapters/prelim.tex:96–109` (definition `:94–102`, bound `:104–106`)" with
  "`chapters/prelim.tex:94–106` (display `:96–100`, bound `:104–106`)". Replace "Policies are stationary randomized `π : S → Δ(A)` (`:62`)" with "… (`:66`)". `:62` is blank, and 96–109 ends inside the V^π(ρ) display at :109–111. In the COVERAGE row #1, use "prelim 94–106".
- **R3 (KLChiSquared.lean module docstring).** Replace "(definitions `eq:TV` `:219–223`, `eq:defn-KL` and `eq:defn-chi2` `:227–235`," with "(definitions `eq:TV` `:222–227`, `eq:defn-KL` and `eq:defn-chi2` `:229–235`,". This matches the Ch1 draft and the TeX, where the TV display is 220–227 and the KL/χ² text and displays are 229–235. CHECK F-P1-1's ":219–223" was itself off.
- **R4 (COVERAGE integration).** COVERAGE.md already has rows for `eq:defn-Vpi-inf` (line 79, "**Partial:**", "lines 89–109") and `eq:Bellman-finite-opt` (line 76, "lines 737–745 and 799–815"). Update or merge those rows instead of adding duplicates. The new scope text supersedes the "Partial" label for #1, and the line ranges should match the docstrings.
- **R5 (G2 PR justification).** The drafts add **six** Ch2 edges, not the five expected in F-P1-4:
  `MDP.InfiniteReturn` (defining module of `trajectoryExpectedValue`, `infiniteDiscountedReturn`, `trajectoryState`),
  `MDP.ForcedActionReturn` (`trajectoryExpectedQ`) and `MDP.FiniteOccupancy` (`DecisionStage.finalState`) are mixed modules.
  For each, the PR must say "defining module of `<def>`; no `*Definitions` split exists".
  `MDP.TrajectoryDefinitions`, `MDP.ActionTrajectoryDefinitions` and `MDP.PolicyEnvironmentDefinitions` are definition modules.
  The PR must also say that `ForcedActionReturn` pulls in `FiniteOptimal` transitively, through `ForcedActionTrajectory`. Ch6.lean → FiniteOccupancy/OptimalTrajectoryValue is the precedent, and the gate forbids only `*Proofs`. This is acceptable, and splitting the definitions out is optional follow-up. Ch1.lean needs no G2 edge. `STATEMENT_FILE_RE` (`Ch(\d+)`), G3 chapter matching (`Ch1Proofs.lean`) and `site/reader/lean.py` (`/Ch\d+\.lean$`) all accept Ch1. Ch1Proofs must `import Formalization.Statements.Ch1`. Add `Probability.KLChiSquared`, `MDP.PrelimDisplays`, `Statements.Ch1` and `Statements.Ch1Proofs` to `Formalization.lean`, and run `--write-allowlists --allow-grow` once.

## Advisory (non-blocking)

- **A1.** In the `Eq_KL_ub_chi2` docstring, add: "`P ≪ Q` is also needed for the `∫⁻` form of χ²: without it KL = ∞ while the integral of the absolutely-continuous part can be finite (e.g. P = δ₁, Q = δ₀)."
- **A2.** In the `Eq_Bellman_finite_opt` docstring, replace "otherwise no deterministic policy exists" with "`Nonempty Action` is the printed 𝒜 = {1,…,A} (`chapters/prelim.tex:36`); each stage already carries a nonempty action set, so it matters only for H = 0."
- **A3.** The d⋆ range could be `:163–176`, because the "valid since π⋆ is deterministic" justification is at :175–176.

## COVERAGE text approval

Once R1, R2 and R4 are applied, the proposed rows (#1–#9, U1–U5, U7–U9, U6 N-row) in the draft docs are **approved**, with the status "Proved". The builder's notes on stationary competitors (U1), Markov competitors (finite horizon) and the `[DecidableEq]` binders are accurate and should stay in the scope column.

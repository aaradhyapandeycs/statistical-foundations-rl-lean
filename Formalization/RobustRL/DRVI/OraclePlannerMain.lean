import Formalization.RobustRL.DRVI.OraclePlannerNumerics

/-!
# Restricted Remark 7.1 (`remark:tv-upper`), final library statement

Source: arXiv:2610.41903v1, `chapters/robust_RL.tex:361–372`.
For every `c_opt ≥ 0`, `C₂ = max(10⁶, 2 c_opt)` works.
-/

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7
open StatisticalRL.ModelBasedPolicyLearning

local instance oracleMainStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

/-- Restricted Remark 7.1: for every `c_opt ≥ 0` there is `C₂ > 0` (namely `max(10⁶, 2 c_opt)`)
such that, under the sample-size condition of Theorem 7.2, with probability at least `1−δ` every
deterministic planner output `f` with empirical robust value gap at most
`c_opt (1−γ)² log(SAN/((1−γ)δ))/N` (in absolute value, at every state) is `ε`-optimal for the
true TV-robust MDP. -/
theorem tv_oracle_planner_guarantee :
  ∀ c_opt : ℝ, 0 ≤ c_opt → ∃ C₂ : ℝ, 0 < C₂ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (σ δ ε : ℝ) (N : ℕ) (hN : 0 < N),
      1 / 4 ≤ M.discount → 0 < σ → σ < 1 → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ Real.sqrt (1 / max (1 - M.discount) σ) →
      C₂ / ((1 - M.discount) ^ 2 * max (1 - M.discount) σ * ε ^ 2) *
          Real.log (Fintype.card State * Fintype.card Action * N /
            ((1 - M.discount) * δ)) ≤ N →
      1 - δ ≤ (samplingLaw M N).real
        {data | ∀ f : State → Action,
          (∀ s, |robustOptimalValue tvBall (empiricalModel M N hN data) σ s -
              robustPolicyValue tvBall (empiricalModel M N hN data) σ (detPolicy f) s| ≤
            c_opt * (1 - M.discount) ^ 2 / N *
              Real.log (Fintype.card State * Fintype.card Action * N /
                ((1 - M.discount) * δ))) →
          ∀ s, robustOptimalValue tvBall M σ s -
            robustPolicyValue tvBall M σ (detPolicy f) s ≤ ε} := by
  intro c_opt hc
  refine ⟨max (10 ^ 6) (2 * c_opt), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro State Action _ _ M σ δ ε N hN hγ hσ0 hσ1 hδ0 hδ1 hε0 hεmax hsample
  classical
  haveI := M.state_nonempty
  haveI := M.action_nonempty
  have hγ1 := M.discount_lt_one
  have hg : 0 < 1 - M.discount := by linarith
  have hγpos : 0 < M.discount := by linarith
  have hm1 : 1 - M.discount ≤ max (1 - M.discount) σ := le_max_left _ _
  have hσm : σ ≤ max (1 - M.discount) σ := le_max_right _ _
  have hm2 : max (1 - M.discount) σ ≤ 1 := max_le (by linarith) hσ1.le
  have hm0 : 0 < max (1 - M.discount) σ := lt_of_lt_of_le hg hm1
  have hεm : ε ^ 2 * max (1 - M.discount) σ ≤ 1 := sq_le_of_le_sqrt_inv hm0 hε0 hεmax
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hS : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos
  have hA : (1 : ℝ) ≤ Fintype.card Action := by exact_mod_cast Fintype.card_pos
  have hg34 : 1 - M.discount ≤ 3 / 4 := by linarith
  have hL := tv_L_lower hS hA hN1 hg hg34 hδ0 hδ1
  set πs := optPolicy (ballFamily tvBall M σ) M
  -- the good event
  have hG : ∀ (x : State) (a : Action) (k : Bool × Fin (N + 1) × Fin (N + 1))
      (c : OffStateCode (Action := Action) x N) (y : State),
      0 ≤ clipFamily tvBall M N hN σ πs x k c y :=
    fun x _ k c y ↦ clipFamily_nonneg tvBall M N hN σ (fun p ↦ tvBall_self_mem p hσ0.le) πs x k c y
  have hGB : ∀ (x : State) (a : Action) (k : Bool × Fin (N + 1) × Fin (N + 1))
      (c : OffStateCode (Action := Action) x N),
      ‖clipFamily tvBall M N hN σ πs x k c‖ ≤ 1 / (1 - M.discount) :=
    fun x _ k c ↦ clipFamily_norm_le tvBall M N hN σ (fun p ↦ tvBall_self_mem p hσ0.le) πs x k c
  have hprob := allRows_indexed_bernstein (ι := Bool × Fin (N + 1) × Fin (N + 1)) M N hN
    (fun x _ k c ↦ clipFamily tvBall M N hN σ πs x k c) hG hGB δ hδ0 hδ1
  -- logarithms
  have hcard : ((Fintype.card (Bool × Fin (N + 1) × Fin (N + 1)) : ℕ) : ℝ) = 2 * (N + 1) ^ 2 := by
    simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]; ring
  set ℓ := Real.log (4 * ((Fintype.card (Bool × Fin (N + 1) × Fin (N + 1)) : ℕ) : ℝ) *
    ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ)) / δ) with hℓdef
  have hℓ : ℓ ≤ 17 * Real.log (Fintype.card State * Fintype.card Action * N /
      ((1 - M.discount) * δ)) := by
    rw [hℓdef, hcard]
    exact tv_ell_le hS hA hN1 hg hg34 hδ0 hδ1
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓdef, hcard]
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ0]
    have : (1 : ℝ) ≤ Fintype.card State * Fintype.card Action :=
      one_le_mul_of_one_le_of_one_le hS hA
    have hN2 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
    have h3 := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num : (1 : ℝ) ≤ 4) (by linarith : (1 : ℝ) ≤ 2 * ((N : ℝ) + 1) ^ 2)) this
    linarith
  -- the sample-size hypothesis
  have hsampleC : max (10 ^ 6) (2 * c_opt) * Real.log (Fintype.card State *
      Fintype.card Action * N / ((1 - M.discount) * δ)) ≤
      N * ((1 - M.discount) ^ 2 * max (1 - M.discount) σ * ε ^ 2) := by
    have hden : 0 < (1 - M.discount) ^ 2 * max (1 - M.discount) σ * ε ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hden] at hsample
    exact hsample
  have hsample' : 10 ^ 6 * Real.log (Fintype.card State * Fintype.card Action * N /
      ((1 - M.discount) * δ)) ≤ N * ((1 - M.discount) ^ 2 * max (1 - M.discount) σ * ε ^ 2) :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hsampleC
  -- planning residual from the oracle requirement
  obtain ⟨hεg, hεm', _, _, _⟩ :=
    numerics_basic hg (by linarith) hm1 hm2 hε0 hεm hL hN1 hsample'
  obtain ⟨hΞ0, hΞ1, hplan⟩ := oracle_planning_bounds hc (le_max_right _ _)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) hg (by linarith) hm0.le hε0 hεm hεm'
    (by linarith) hNR hsampleC
  have hB'0 : 0 ≤ 1 / (1 - M.discount + M.discount * σ) := by
    have : 0 < 1 - M.discount + M.discount * σ := by
      have := mul_nonneg M.discount_nonneg hσ0.le
      linarith
    positivity
  have hB' := tv_span_constant hγ hγ1 hσ0.le
  have hnum := tv_selfBoundExpr_le_of_planning hγ hγ1 hm1 hm2 hσ0.le hσm hε0 hεm hL hℓ0 hℓ hN1
    hsample' hB'0 hB' hΞ0 hΞ1 (by simpa using hplan)
  refine le_of_lt (hprob.trans_le (measureReal_mono ?_ (measure_ne_top _ _)))
  intro data hdata f hf s
  have hgap := tv_good_gap_of_valueGap M hσ0 hσ1.le hγpos N hN data hℓ0 hdata f
    (fun t ↦ (le_abs_self _).trans (hf t)) s
  exact hgap.trans hnum

end StatisticalRL.RobustRL.DRVI

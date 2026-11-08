import Formalization.RobustRL.DRVI.Thm72

/-!
# Corrected Theorem 7.2 (TV), final statement

`thm7_2_corrected_holds : Thm7_2_corrected` with `C₁ = 2`, `C₂ = 10⁶`.
-/

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7
open StatisticalRL.ModelBasedPolicyLearning

local instance thm72MainStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

theorem sq_le_of_le_sqrt_inv {ε m : ℝ} (hm : 0 < m) (hε : 0 < ε)
    (h : ε ≤ Real.sqrt (1 / m)) : ε ^ 2 * m ≤ 1 := by
  have h2 : ε ^ 2 ≤ 1 / m := by
    calc ε ^ 2 ≤ Real.sqrt (1 / m) ^ 2 := pow_le_pow_left₀ hε.le h 2
      _ = 1 / m := Real.sq_sqrt (by positivity)
  rw [le_div_iff₀ hm] at h2
  exact h2

theorem thm7_2_corrected_holds : Thm7_2_corrected := by
  refine ⟨2, 10 ^ 6, by norm_num, by norm_num, ?_⟩
  intro State Action _ _ M σ δ ε N hN hγ hσ0 hσ1 hδ0 hδ1 hε0 hεmax hsample T hT pick hpick
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
    have : (1 : ℝ) ≤ Fintype.card State * Fintype.card Action := by nlinarith
    nlinarith
  -- the sample-size hypothesis
  have hsample' : 10 ^ 6 * Real.log (Fintype.card State * Fintype.card Action * N /
      ((1 - M.discount) * δ)) ≤ N * ((1 - M.discount) ^ 2 * max (1 - M.discount) σ * ε ^ 2) := by
    have hden : 0 < (1 - M.discount) ^ 2 * max (1 - M.discount) σ * ε ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hden] at hsample
    exact hsample
  -- planning residual
  have hΞ : 2 * (M.discount ^ T / (1 - M.discount)) ≤ 2 * (1 - M.discount) / N ^ 2 := by
    have h := pow_le_sq_of_iterations hγpos hγ1 hNR (T := T) (by simpa using hT)
    rw [div_pow] at h
    have : M.discount ^ T / (1 - M.discount) ≤ (1 - M.discount) ^ 2 / N ^ 2 / (1 - M.discount) :=
      div_le_div_of_nonneg_right h hg.le
    have e : (1 - M.discount) ^ 2 / N ^ 2 / (1 - M.discount) = (1 - M.discount) / N ^ 2 := by
      field_simp
    rw [e] at this
    have e2 : 2 * (1 - M.discount) / (N : ℝ) ^ 2 = 2 * ((1 - M.discount) / N ^ 2) := by ring
    rw [e2]
    linarith
  have hΞ0 : 0 ≤ 2 * (M.discount ^ T / (1 - M.discount)) := by positivity
  have hB'0 : 0 ≤ 1 / (1 - M.discount + M.discount * σ) := by
    have : 0 < 1 - M.discount + M.discount * σ := by nlinarith
    positivity
  have hB' := tv_span_constant hγ hγ1 hσ0.le
  have hnum := tv_selfBoundExpr_le hγ hγ1 hm1 hm2 hσ0.le hσm hε0 hεm hL hℓ0 hℓ hN1 hsample'
    hB'0 hB' hΞ0 hΞ
  refine le_of_lt (hprob.trans_le (measureReal_mono ?_ (measure_ne_top _ _)))
  intro data hdata s
  have hgap := tv_good_gap M hσ0 hσ1.le hγpos N hN data hℓ0 hdata T (pick data) (hpick data) s
  exact hgap.trans hnum

end StatisticalRL.RobustRL.DRVI

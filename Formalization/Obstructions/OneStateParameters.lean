import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Feasibility of the printed Theorem 3.7 parameter range at S=1, A=16. -/

namespace StatisticalRL.Obstructions

/-- Every positive proposed constant admits a positive accuracy and one
sample in the paper's printed parameter range at γ=2/3, S=1 and A=16. -/
theorem oneState_parameter_feasible (c : ℝ) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / (32 * (1 - (2 : ℝ) / 3)) ∧
      1 ≤ c * Real.log 16 / ((1 - (2 : ℝ) / 3) ^ 3 * ε ^ 2) := by
  let x : ℝ := 27 * c * Real.log 16
  have hlog : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hx : 0 < x := by dsimp [x]; positivity
  let ε : ℝ := min (1 / 64) x
  have he : 0 < ε := lt_min (by norm_num) hx
  have he64 : ε ≤ 1 / 64 := min_le_left _ _
  have hex : ε ≤ x := min_le_right _ _
  have he1 : ε ≤ 1 := by linarith
  have he_sq : ε ^ 2 ≤ x := by
    have hprod : 0 ≤ ε * (1 - ε) := mul_nonneg he.le (sub_nonneg.mpr he1)
    nlinarith only [hprod, hex]
  have hdiv : (1 : ℝ) ≤ x / ε ^ 2 := (one_le_div₀ (sq_pos_of_pos he)).2 he_sq
  refine ⟨ε, he, ?_, ?_⟩
  · norm_num at *
    linarith
  · convert hdiv using 1; dsimp [x]; ring

/-- The concrete singleton-state instance also meets the paper's stated
discount and size restrictions. `N = 1` is encoded by the left-hand side of
the sample-size inequality. -/
theorem oneState_theorem37_hypotheses_feasible (c : ℝ) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / (32 * (1 - (2 : ℝ) / 3)) ∧
      (2 : ℝ) / 3 ≤ 2 / 3 ∧ (2 : ℝ) / 3 < 1 ∧
      16 ≤ Fintype.card (Fin 1) * Fintype.card (Fin 16) ∧
      1 ≤ c * Real.log 16 / ((1 - (2 : ℝ) / 3) ^ 3 * ε ^ 2) := by
  obtain ⟨ε, hpos, hupper, hsample⟩ := oneState_parameter_feasible c hc
  refine ⟨ε, hpos, hupper, ?_, ?_, ?_, hsample⟩ <;> norm_num

end StatisticalRL.Obstructions

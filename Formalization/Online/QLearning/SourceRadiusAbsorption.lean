import Formalization.Online.QLearning.SourceLogAbsorption

/-! Nondegenerate source-log radius comparison. -/
namespace StatisticalRL.OnlineRL

theorem qLearning_source_radius_absorb (A x δ : ℝ) (hA : 0 ≤ A) (hx : 2 ≤ x)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.sqrt (A*Real.log (4*x/δ)) ≤ 2*Real.sqrt (A*Real.log (x/δ)) := by
  have hy : 1 ≤ x/δ := by rw [le_div_iff₀ hδ]; linarith
  have hl : 0 ≤ Real.log (x/δ) := Real.log_nonneg hy
  have hp : 0 ≤ A*Real.log (x/δ) := mul_nonneg hA hl
  have hlog := qLearning_source_log_absorb x δ hx hδ hδ1
  have hb : A*Real.log (4*x/δ) ≤ 4*(A*Real.log (x/δ)) := by nlinarith
  calc
    _ ≤ Real.sqrt (4*(A*Real.log (x/δ))) := Real.sqrt_le_sqrt hb
    _ = 2*Real.sqrt (A*Real.log (x/δ)) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      have h4 : Real.sqrt (4:ℝ) = 2 := by
        have hh := Real.sqrt_sq_eq_abs (2:ℝ)
        norm_num at hh ⊢
        exact hh
      rw [h4]
end StatisticalRL.OnlineRL

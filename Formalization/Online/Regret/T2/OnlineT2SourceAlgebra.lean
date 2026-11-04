import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Scalar final step for the source T₂ bonus inequality. The extra first-visit
charge is explicit and absorbed using the source-sized iota lower bound. -/
namespace StatisticalRL.OnlineRL

theorem onlineT2_coarse_to_source
    (A H B L I c₁ c₂ T : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hT : 0 ≤ T)
    (hi1 : 8 * c₁^2 * B * L ≤ I) (hi2 : 8 * c₂ * B * L ≤ I) (hi4 : 4 ≤ I) :
    H * A + c₁ * Real.sqrt (2 * A * B * L * T) + 2 * c₂ * H * A * B * L ≤
      (1 / 2 : ℝ) * Real.sqrt (A * T * I) + (1 / 2 : ℝ) * A * H * I := by
  have hI : 0 ≤ I := by linarith
  have hfirst : 0 ≤ 2 * A * B * L * T := by positivity
  have hlast : 0 ≤ A * T * I := by positivity
  have hcoef := mul_le_mul_of_nonneg_right hi1 (show 0 ≤ A * T by positivity)
  have hroot : c₁ * Real.sqrt (2 * A * B * L * T) ≤ (1 / 2 : ℝ) * Real.sqrt (A * T * I) := by
    have hl : 0 ≤ c₁ * Real.sqrt (2 * A * B * L * T) := by positivity
    have hr : 0 ≤ (1 / 2 : ℝ) * Real.sqrt (A * T * I) := by positivity
    have hsq : (c₁ * Real.sqrt (2 * A * B * L * T))^2 ≤ ((1 / 2 : ℝ) * Real.sqrt (A * T * I))^2 := by
      nlinarith [Real.sq_sqrt hfirst, Real.sq_sqrt hlast, hcoef]
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left hi2 (show 0 ≤ A * H by positivity)
  have hzero := mul_le_mul_of_nonneg_left hi4 (show 0 ≤ A * H by positivity)
  nlinarith
end StatisticalRL.OnlineRL

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Scalar step for MVP T2. The factor four in the retained-count
budget is handled directly. This is an intermediate lemma, not a source event. -/
namespace StatisticalRL.OnlineRL

theorem mvpT2_coarse_to_source
    (A H B L I c₁ c₂ T : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hT : 0 ≤ T)
    (hi1 : 16 * c₁^2 * B * L ≤ I)
    (hi2 : 8 * B * (1 + c₂ * L) ≤ I) :
    4 * A * H * B + c₁ * Real.sqrt (4 * A * B * L * T) +
      4 * c₂ * H * A * B * L ≤
      (1 / 2 : ℝ) * Real.sqrt (A * T * I) + (1 / 2 : ℝ) * A * H * I := by
  have hI : 0 ≤ I := le_trans (by positivity : 0 ≤ 16 * c₁^2 * B * L) hi1
  have hleft : 0 ≤ 4 * A * B * L * T := by positivity
  have hright : 0 ≤ A * T * I := by positivity
  have hroot : c₁ * Real.sqrt (4 * A * B * L * T) ≤
      (1 / 2 : ℝ) * Real.sqrt (A * T * I) := by
    have hl : 0 ≤ c₁ * Real.sqrt (4 * A * B * L * T) := by positivity
    have hr : 0 ≤ (1 / 2 : ℝ) * Real.sqrt (A * T * I) := by positivity
    have hs := mul_le_mul_of_nonneg_right hi1 (show 0 ≤ A * T by positivity)
    have hsq : (c₁ * Real.sqrt (4 * A * B * L * T))^2 ≤
        ((1 / 2 : ℝ) * Real.sqrt (A * T * I))^2 := by
      nlinarith [Real.sq_sqrt hleft, Real.sq_sqrt hright]
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left hi2 (show 0 ≤ A * H by positivity)
  nlinarith
end StatisticalRL.OnlineRL

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! OnlineW1AbsorptionAlgebra: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL

theorem onlineW1_coarse_to_iota_algebra
    (A H L Q I p d : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hp : 0 ≤ p) (hd : 0 ≤ d)
    (hi : 256 * L * Q ≤ I) (hi48 : 48 ≤ I) :
    H * (3 * A) + Real.sqrt (2 * L * (2 * p + 2 * d)) * Real.sqrt (A * Q) +
        (2 * H * L / 3) * (A * Q) ≤
      (1 / 8 : ℝ) * Real.sqrt (A * p * I) +
      (1 / 8 : ℝ) * Real.sqrt (A * d * I) +
      (1 / 8 : ℝ) * A * H * I := by
  have hI : 0 ≤ I := by linarith
  have hx : 0 ≤ 2 * L * (2 * p + 2 * d) := by positivity
  have hy : 0 ≤ A * Q := mul_nonneg hA hQ
  have hpI : 0 ≤ A * p * I := by positivity
  have hdI : 0 ≤ A * d * I := by positivity
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have hsp := Real.sq_sqrt hpI
  have hsd := Real.sq_sqrt hdI
  have hcross := mul_nonneg (Real.sqrt_nonneg (A * p * I)) (Real.sqrt_nonneg (A * d * I))
  have hcoef := mul_le_mul_of_nonneg_right hi (show 0 ≤ A * (p + d) by positivity)
  have hroot : Real.sqrt (2 * L * (2 * p + 2 * d)) * Real.sqrt (A * Q) ≤
      (1 / 8 : ℝ) * Real.sqrt (A * p * I) + (1 / 8 : ℝ) * Real.sqrt (A * d * I) := by
    have hleft : 0 ≤ Real.sqrt (2 * L * (2 * p + 2 * d)) * Real.sqrt (A * Q) := by positivity
    have hright : 0 ≤ (1 / 8 : ℝ) * Real.sqrt (A * p * I) + (1 / 8 : ℝ) * Real.sqrt (A * d * I) := by positivity
    have hsq : (Real.sqrt (2 * L * (2 * p + 2 * d)) * Real.sqrt (A * Q))^2 ≤
        ((1 / 8 : ℝ) * Real.sqrt (A * p * I) + (1 / 8 : ℝ) * Real.sqrt (A * d * I))^2 := by
      nlinarith [hsx, hsy, hsp, hsd, hcross, hcoef]
    nlinarith
  have hAH : 0 ≤ A * H := mul_nonneg hA hH
  have hlinear := mul_le_mul_of_nonneg_left hi hAH
  have hsmall := mul_le_mul_of_nonneg_left hi48 hAH
  nlinarith
end StatisticalRL.OnlineRL

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Deterministic square-root comparison used in the source T₃ radius. -/

namespace StatisticalRL.OnlineRL

theorem onlineVarianceRadius_le_policy_difference
    (u p d L : ℝ) (hu : 0 ≤ u) (hp : 0 ≤ p) (hd : 0 ≤ d) (hL : 0 ≤ L)
    (hcompare : u ≤ 2 * p + 2 * d) :
    Real.sqrt (8 * u * L) ≤ 4 * Real.sqrt (p * L) + 4 * Real.sqrt (d * L) := by
  have hmul := mul_le_mul_of_nonneg_right hcompare hL
  have hsu := Real.sq_sqrt (show 0 ≤ 8 * u * L by positivity)
  have hsp := Real.sq_sqrt (mul_nonneg hp hL)
  have hsd := Real.sq_sqrt (mul_nonneg hd hL)
  have hcross := mul_nonneg (Real.sqrt_nonneg (p * L)) (Real.sqrt_nonneg (d * L))
  have hsquares : (Real.sqrt (8 * u * L))^2 ≤
      (4 * Real.sqrt (p * L) + 4 * Real.sqrt (d * L))^2 := by
    nlinarith
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp hsquares

end StatisticalRL.OnlineRL

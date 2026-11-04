import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Scalar absorption for the W₂ source iota. -/
namespace StatisticalRL.OnlineRL

theorem onlineW2_coarse_to_iota_algebra
    (S A H L Q I d : ℝ)
    (hS : 1 ≤ S) (hA : 0 ≤ A) (hH : 0 ≤ H) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hd : 0 ≤ d) (hi : 256 * L * Q ≤ I) (hi48 : 48 ≤ I) :
    H * (3 * A) + Real.sqrt (2 * (S * L) * d) * Real.sqrt (A * Q) + S * H * L * (A * Q) ≤
      (1 / 8 : ℝ) * Real.sqrt (S * A * d * I) + (1 / 8 : ℝ) * S * A * H * I := by
  have hS0 : 0 ≤ S := by linarith
  have hI : 0 ≤ I := by linarith
  have hx : 0 ≤ 2 * (S * L) * d := by positivity
  have hy : 0 ≤ A * Q := by positivity
  have hz : 0 ≤ S * A * d * I := by positivity
  have hcoef := mul_le_mul_of_nonneg_right hi (show 0 ≤ S * A * d by positivity)
  have hroot : Real.sqrt (2 * (S * L) * d) * Real.sqrt (A * Q) ≤
      (1 / 8 : ℝ) * Real.sqrt (S * A * d * I) := by
    have hleft : 0 ≤ Real.sqrt (2 * (S * L) * d) * Real.sqrt (A * Q) := by positivity
    have hright : 0 ≤ (1 / 8 : ℝ) * Real.sqrt (S * A * d * I) := by positivity
    have hx' := Real.sq_sqrt hx
    have hy' := Real.sq_sqrt hy
    have hz' := Real.sq_sqrt hz
    nlinarith [hx', hy', hz', hcoef]
  have hbase : 0 ≤ A * H := by positivity
  have hlarge := mul_le_mul_of_nonneg_left hi (show 0 ≤ S * A * H by positivity)
  have hsmall := mul_le_mul_of_nonneg_left hi48 hbase
  have hSA : A * H ≤ S * A * H := by nlinarith [mul_nonneg (sub_nonneg.mpr hS) hbase]
  nlinarith
end StatisticalRL.OnlineRL

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Scalar radius comparisons for the corrected joint MVP T234 estimate. -/
namespace StatisticalRL.OnlineRL

theorem mvpJoint_T3_radius_absorb (V H q qt I : ℝ)
    (hV : 0 ≤ V) (hH : 0 ≤ H) (hq : 0 ≤ q) (hqt : 0 ≤ qt)
    (hqtq : qt ≤ 2*q) (hi1 : 16*q ≤ I) (hi2 : 10*q ≤ I) :
    Real.sqrt (8*V*qt) + 5*H*qt ≤ Real.sqrt (V*I) + H*I := by
  have hm := mul_le_mul_of_nonneg_left hi1 hV
  have ht := mul_le_mul_of_nonneg_left hqtq hV
  have hr : Real.sqrt (8*V*qt) ≤ Real.sqrt (V*I) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hl := mul_le_mul_of_nonneg_left hi2 hH
  have htail := mul_le_mul_of_nonneg_left hqtq hH
  nlinarith

theorem mvpJoint_T4_radius_absorb (K H q qt I : ℝ)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hqtq : qt ≤ 2*q) (hi : 4*q ≤ I) :
    Real.sqrt (2*K*H^2*qt) ≤ Real.sqrt (K*H^2*I) := by
  apply Real.sqrt_le_sqrt
  have h := mul_le_mul_of_nonneg_left (show 2*qt ≤ I by linarith)
    (show 0 ≤ K*H^2 by positivity)
  nlinarith
end StatisticalRL.OnlineRL

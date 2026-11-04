import Mathlib.Tactic

/-! Scalar absorption once the explicit finite-union log is bounded. -/
namespace StatisticalRL.OnlineRL

/-- The corrected allocation supplies q≥1. A coarse explicit log-cardinality
bound of 40*d*x²*z+q is absorbed by the unchanged 40000 source factor. -/
theorem mvp_logBudget_absorbed40 (d x z q L : ℝ)
    (hd : 1 ≤ d) (hx : 1 ≤ x) (hz : 1/2 ≤ z) (hq : 1 ≤ q)
    (hL : L ≤ 40*d*x^2*z + q) :
    32*L*x ≤ d*(40000*x^3*z*q) := by
  have hx2 : 1 ≤ x^2 := by nlinarith
  have hdx : 1 ≤ d*x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hx2)]
  have hB : (1/2:ℝ) ≤ d*x^2*z := by
    have hm := mul_le_mul_of_nonneg_right hdx (show 0 ≤ z by linarith)
    nlinarith
  have hBq : d*x^2*z ≤ d*x^2*z*q := by
    have hm := mul_nonneg (show 0 ≤ d*x^2*z by positivity) (sub_nonneg.mpr hq)
    nlinarith
  have hqB : q ≤ 2*d*x^2*z*q := by
    have hm := mul_le_mul_of_nonneg_right hB (show 0 ≤ q by linarith)
    nlinarith
  have hL' : L ≤ 42*d*x^2*z*q := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hL' (show 0 ≤ 32*x by linarith)
  nlinarith
end StatisticalRL.OnlineRL

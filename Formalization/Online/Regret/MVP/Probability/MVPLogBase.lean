import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Bounding the finite-profile base logarithm by the source log factors. -/
namespace StatisticalRL.OnlineRL

theorem mvp_log4dK_le (d K : ℝ) (hd : 1 ≤ d) (hK : 2 ≤ K) :
    Real.log (4*d*K) ≤ 8 * (Real.log K / Real.log 2) * Real.log (3*d) := by
  have hdpos : 0 < d := by linarith
  have hKpos : 0 < K := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hx : 1 ≤ Real.log K / Real.log 2 := by
    apply (le_div_iff₀ hl2).2
    simpa using Real.log_le_log (by norm_num : (0:ℝ)<2) hK
  have hz : (1/2:ℝ) ≤ Real.log (3*d) := by
    have hbase : (2:ℝ) ≤ 3*d := by nlinarith
    have h1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) hbase
    norm_num at h1
    linarith
  have hlogd : Real.log d ≤ Real.log (3*d) :=
    Real.log_le_log hdpos (by nlinarith)
  have hlogK : Real.log K ≤ Real.log K / Real.log 2 := by
    have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
    apply (le_div_iff₀ hl2).2
    nlinarith
  have hlog4 : Real.log 4 ≤ 2 := by
    have h := hl2le
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hxz : Real.log (3*d) ≤ (Real.log K / Real.log 2) * Real.log (3*d) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ Real.log (3*d) by linarith)]
  have hxx : Real.log K / Real.log 2 ≤ 2 * (Real.log K / Real.log 2) * Real.log (3*d) := by
    nlinarith [mul_nonneg (show 0 ≤ Real.log K / Real.log 2 by linarith)
      (show 0 ≤ 2*Real.log (3*d)-1 by linarith)]
  have hconst : (2:ℝ) ≤ 4 * (Real.log K / Real.log 2) * Real.log (3*d) := by nlinarith
  rw [Real.log_mul (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) (ne_of_gt hdpos)) (ne_of_gt hKpos),
    Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (ne_of_gt hdpos)]
  linarith
end StatisticalRL.OnlineRL

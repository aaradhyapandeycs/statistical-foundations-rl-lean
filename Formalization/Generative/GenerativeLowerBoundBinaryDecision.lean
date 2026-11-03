import Formalization.Generative.GenerativeLowerBoundBinaryEntropy

/-! Scalar binary-decision step toward Fano. -/
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- For 0 < q < 1, binary relative entropy dominates t log(1/q) minus
binary entropy. This remains valid at t=0 and t=1. -/
theorem binary_relative_entropy_lower (t q : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hq : 0 < q) (hq1 : q < 1) :
    t * Real.log (1 / q) - Real.log 2 ≤
      t * Real.log (t / q) + (1 - t) * Real.log ((1 - t) / (1 - q)) := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hq10 : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  have hlog : Real.log (1 - q) ≤ 0 := Real.log_nonpos (sub_pos.mpr hq1).le (by linarith)
  have hprod : 0 ≤ -((1 - t) * Real.log (1 - q)) :=
    neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hlog)
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he := binary_entropy_le_log_two t ht ht1
  by_cases ht0 : t = 0
  · subst t
    simp only [zero_mul, zero_div, Real.log_zero, sub_zero, one_mul, zero_sub] at *
    rw [Real.log_div (by norm_num) hq10, Real.log_one]
    linarith
  by_cases htt : t = 1
  · subst t
    simp only [sub_self, zero_mul, zero_div, Real.log_zero, one_mul, sub_zero] at *
    linarith
  have htone : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm htt)
  rw [Real.log_div ht0 hq0, Real.log_div htone hq10,
    Real.log_div (by norm_num) hq0, Real.log_one]
  nlinarith

end StatisticalRL.GenerativeLowerBound

import Formalization.Probability.EmpiricalBernsteinSharp.BennettPositiveRemainder

/-! Private uncompiled scalar comparison for the self-bounding ODE. -/
namespace StatisticalRL.SharpBernstein

theorem exponential_remainder_scale_lower (a theta : ℝ)
    (ha : 1 ≤ a) (htheta : 0 ≤ theta) :
    a^2 * (Real.exp theta-1-theta) ≤ Real.exp (a*theta)-1-a*theta := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 ≤ 1/a := by positivity
  have hx1 : 1/a ≤ 1 := by
    rw [div_le_one ha0]
    linarith
  have h := exp_remainder_scaled_nonnegative (a*theta) (1/a)
    (mul_nonneg ha0.le htheta) hx0 hx1
  have heq : (a*theta)*(1/a) = theta := by field_simp
  rw [heq] at h
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg a)
  field_simp at hmul
  nlinarith

end StatisticalRL.SharpBernstein

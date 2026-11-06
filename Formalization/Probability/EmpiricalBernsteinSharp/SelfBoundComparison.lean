import Formalization.Probability.EmpiricalBernsteinSharp.SelfBoundExponentialScale
import Formalization.Probability.EmpiricalBernsteinSharp.BennettNegativeRemainder

/-! Private scalar comparison for the self-bounding entropy differential
inequality. No stochastic MGF or concentration claim is made here. -/
namespace StatisticalRL.SharpBernstein

/-- The proposed comparison function has the required differential sign. -/
theorem self_bound_comparison_sign (a m theta : ℝ)
    (ha : 1 ≤ a) (hm : 0 ≤ m) (htheta : 0 ≤ theta) :
    0 ≤ m/a*(1-Real.exp (-a*theta)) -
      m*Real.exp (-a*theta)*(theta+a*(Real.exp theta-1-theta)) := by
  have ha0 : 0 < a := by linarith
  have hscale := exponential_remainder_scale_lower a theta ha htheta
  have hexp : Real.exp (-(a*theta))*Real.exp (a*theta) = 1 := by
    rw [← Real.exp_add]
    rw [neg_add_cancel, Real.exp_zero]
  have hnonneg : 0 ≤ m/a*Real.exp (-a*theta) := by positivity
  have h := mul_nonneg hnonneg (sub_nonneg.mpr hscale)
  have hid : m/a*Real.exp (-a*theta) *
      ((Real.exp (a*theta)-1-a*theta)-a^2*(Real.exp theta-1-theta)) =
      m/a*(1-Real.exp (-a*theta)) -
        m*Real.exp (-a*theta)*(theta+a*(Real.exp theta-1-theta)) := by
    have he := congrArg (fun x : ℝ ↦ m*x) hexp
    field_simp [ne_of_gt ha0]
    nlinarith [he]
  rwa [hid] at h

/-- The centered comparison is bounded by the sub-Gaussian quadratic. -/
theorem self_bound_comparison_quadratic (a m theta : ℝ)
    (ha : 1 ≤ a) (hm : 0 ≤ m) (htheta : 0 ≤ theta) :
    -(m/a)*(1-Real.exp (-a*theta)) + theta*m ≤ a*m*theta^2/2 := by
  have ha0 : 0 < a := by linarith
  have hz : -a*theta ≤ 0 := by nlinarith [mul_nonneg ha0.le htheta]
  have h := exp_le_quadratic_of_nonpos (-a*theta) hz
  have hmul := mul_le_mul_of_nonneg_left h (div_nonneg hm ha0.le)
  field_simp at hmul ⊢
  nlinarith

end StatisticalRL.SharpBernstein

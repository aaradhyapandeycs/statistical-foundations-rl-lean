import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Private, uncompiled analytic candidate for the exact Bennett inversion.
It uses a finite lower truncation of the log series; no concentration theorem
or source result is assumed. -/
namespace StatisticalRL.Probability

/-- A nonnegative polynomial certificate for the eight-term log truncation. -/
theorem bennett_inverse_polynomial (v : ℝ) (hv : 0 ≤ v) :
    let u := v + v^2 / 6
    0 ≤ (1 + u) * (2*u*(u+2)^14 + (2/3 : ℝ)*u^3*(u+2)^12 +
        (2/5 : ℝ)*u^5*(u+2)^10 + (2/7 : ℝ)*u^7*(u+2)^8 +
        (2/9 : ℝ)*u^9*(u+2)^6 + (2/11 : ℝ)*u^11*(u+2)^4 +
        (2/13 : ℝ)*u^13*(u+2)^2 + (2/15 : ℝ)*u^15) -
      (u + v^2/2)*(u+2)^15 := by
  dsimp only
  ring_nf
  positivity

/-- Exact inversion inequality for the Bennett function at the one-third
linear radius. This is analytic infrastructure, not a tail bound. -/
theorem bennett_inverse_one_third (t : ℝ) (ht : 0 ≤ t) :
    let u := Real.sqrt (2*t) + t/3
    t ≤ (1+u) * Real.log (1+u) - u := by
  let v : ℝ := Real.sqrt (2*t)
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hv2 : v^2 = 2*t := Real.sq_sqrt (by positivity)
  let u : ℝ := v + v^2/6
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hD : 0 < u+2 := by linarith
  let r : ℝ := u/(u+2)
  have hr0 : 0 ≤ r := div_nonneg hu hD.le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one hD]
    linarith
  have heq : (1+r)/(1-r) = 1+u := by
    have hrne : 1-r ≠ 0 := ne_of_gt (by linarith : 0 < 1-r)
    dsimp [r]
    field_simp [ne_of_gt hD]
    ring
  have hs := Real.sum_range_le_log_div hr0 hr1 8
  rw [heq] at hs
  norm_num [Finset.sum_range_succ] at hs
  have hlog : 2 * (r + r^3/3 + r^5/5 + r^7/7 + r^9/9 + r^11/11 + r^13/13 + r^15/15) ≤
      Real.log (1+u) := by linarith
  have hp := bennett_inverse_polynomial v hv
  change 0 ≤ (1 + u) * (2*u*(u+2)^14 + (2/3 : ℝ)*u^3*(u+2)^12 +
        (2/5 : ℝ)*u^5*(u+2)^10 + (2/7 : ℝ)*u^7*(u+2)^8 +
        (2/9 : ℝ)*u^9*(u+2)^6 + (2/11 : ℝ)*u^11*(u+2)^4 +
        (2/13 : ℝ)*u^13*(u+2)^2 + (2/15 : ℝ)*u^15) -
      (u + v^2/2)*(u+2)^15 at hp
  have hpdiv := div_nonneg hp (pow_nonneg hD.le 15)
  have hident : ((1 + u) * (2*u*(u+2)^14 + (2/3 : ℝ)*u^3*(u+2)^12 +
        (2/5 : ℝ)*u^5*(u+2)^10 + (2/7 : ℝ)*u^7*(u+2)^8 +
        (2/9 : ℝ)*u^9*(u+2)^6 + (2/11 : ℝ)*u^11*(u+2)^4 +
        (2/13 : ℝ)*u^13*(u+2)^2 + (2/15 : ℝ)*u^15) -
      (u + v^2/2)*(u+2)^15) / (u+2)^15 =
      (1+u) * (2 * (r + r^3/3 + r^5/5 + r^7/7 + r^9/9 +
        r^11/11 + r^13/13 + r^15/15)) - u - v^2/2 := by
    dsimp [r]
    field_simp [ne_of_gt hD]
    ring
  rw [hident] at hpdiv
  have hscaled := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ 1+u)
  have hu_eq : u = Real.sqrt (2*t) + t/3 := by
    change v + v^2/6 = v + t/3
    linarith [hv2]
  dsimp only
  rw [← hu_eq]
  linarith [hv2]
end StatisticalRL.Probability

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Private uncompiled deterministic assembly of the literal 7/3 source
radius. No concentration assumption is introduced into a source theorem. -/
namespace StatisticalRL.Probability

theorem empirical_bernstein_sharp_radius_algebra (n B t v e : ℝ)
    (hn : 1 < n) (hB : 0 ≤ B) (ht : 0 ≤ t) (hv : 0 ≤ v) (he : 0 ≤ e)
    (hstd : Real.sqrt v ≤ Real.sqrt (n/(n-1)*e) + B*Real.sqrt (2*t/(n-1))) :
    Real.sqrt (2*v*t/n) + B*t/(3*n) ≤
      Real.sqrt (2*e*t/(n-1)) + 7*B*t/(3*(n-1)) := by
  let c := Real.sqrt (2*t/n)
  let d := Real.sqrt (2*t/(n-1))
  let s := Real.sqrt (n/(n-1)*e)
  let σ := Real.sqrt v
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  have hc2 : c^2 = 2*t/n := Real.sq_sqrt (by positivity)
  have hd2 : d^2 = 2*t/(n-1) := Real.sq_sqrt (by positivity)
  have hs2 : s^2 = n/(n-1)*e := Real.sq_sqrt (by positivity)
  have hσ2 : σ^2 = v := Real.sq_sqrt hv
  have hcd : c ≤ d := by
    dsimp [c, d]
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*t) hn1
    linarith
  have hroot1 : c*σ = Real.sqrt (2*v*t/n) := by
    have hr : 0 ≤ Real.sqrt (2*v*t/n) := Real.sqrt_nonneg _
    have hr2 := Real.sq_sqrt (show 0 ≤ 2*v*t/n by positivity)
    have heq : (c*σ)^2 = 2*v*t/n := by rw [mul_pow, hc2, hσ2]; ring
    nlinarith [mul_nonneg hc hσ]
  have hroot2 : c*s = Real.sqrt (2*e*t/(n-1)) := by
    have hr : 0 ≤ Real.sqrt (2*e*t/(n-1)) := Real.sqrt_nonneg _
    have hr2 := Real.sq_sqrt (show 0 ≤ 2*e*t/(n-1) by positivity)
    have heq : (c*s)^2 = 2*e*t/(n-1) := by
      rw [mul_pow, hc2, hs2]
      field_simp
      <;> ring
    nlinarith [mul_nonneg hc hs]
  have hscaled := mul_le_mul_of_nonneg_left hstd hc
  have hcross : c*(B*d) ≤ B*(2*t/(n-1)) := by
    have h := mul_le_mul_of_nonneg_right hcd (mul_nonneg hB hd)
    have hscale2 := congrArg (fun x : ℝ ↦ B*x) hd2
    nlinarith [hscale2]
  have hlin : B*t/(3*n) ≤ B*t/(3*(n-1)) := by
    apply div_le_div_of_nonneg_left (mul_nonneg hB ht) (by positivity : 0 < 3*(n-1))
    linarith
  change c*σ ≤ c*(s+B*d) at hscaled
  have hcross' : c*(B*d) ≤ 6*(B*t/(3*(n-1))) := by
    convert hcross using 1 <;> field_simp [ne_of_gt hn1] <;> ring
  rw [← hroot1, ← hroot2]
  have hseven : 7*B*t/(3*(n-1)) = 7*(B*t/(3*(n-1))) := by ring
  rw [hseven]
  nlinarith

end StatisticalRL.Probability

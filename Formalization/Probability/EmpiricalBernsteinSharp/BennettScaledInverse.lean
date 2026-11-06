import Formalization.Probability.EmpiricalBernsteinSharp.BennettInverseScalar

/-! Private uncompiled scaling of the exact Bennett inverse. -/
namespace StatisticalRL.SharpBernstein

theorem bennett_scaled_inverse (n v B t : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hB : 0 < B) (ht : 0 ≤ t) :
    t ≤ (n*v/B^2) *
      ((1 + B*(Real.sqrt (2*v*t/n) + B*t/(3*n))/v) *
          Real.log (1 + B*(Real.sqrt (2*v*t/n) + B*t/(3*n))/v) -
        B*(Real.sqrt (2*v*t/n) + B*t/(3*n))/v) := by
  let q : ℝ := t*B^2/(n*v)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hinv := StatisticalRL.Probability.bennett_inverse_one_third q hq
  dsimp only at hinv
  have hs : B * Real.sqrt (2*v*t/n) / v = Real.sqrt (2*q) := by
    have hl : 0 ≤ B * Real.sqrt (2*v*t/n) / v := by positivity
    have hr : 0 ≤ Real.sqrt (2*q) := Real.sqrt_nonneg _
    have hs1 := Real.sq_sqrt (show 0 ≤ 2*v*t/n by positivity)
    have hs2 := Real.sq_sqrt (show 0 ≤ 2*q by positivity)
    have heq : (B * Real.sqrt (2*v*t/n) / v)^2 = 2*q := by
      rw [div_pow, mul_pow, hs1]
      dsimp [q]
      field_simp
      <;> ring
    nlinarith
  have he : B*(Real.sqrt (2*v*t/n) + B*t/(3*n))/v =
      Real.sqrt (2*q) + q/3 := by
    rw [← hs]
    dsimp [q]
    field_simp
    <;> ring
  rw [he]
  have hfactor : 0 ≤ n*v/B^2 := by positivity
  have := mul_le_mul_of_nonneg_left hinv hfactor
  have hcancel : (n*v/B^2)*q = t := by
    dsimp [q]
    field_simp
  simpa only [hcancel] using this

end StatisticalRL.SharpBernstein

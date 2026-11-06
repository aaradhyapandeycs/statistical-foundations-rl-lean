import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! Private uncompiled scalar derivative-sign ingredient for the self-bound
comparison. No limiting or probabilistic assertion is made here. -/
namespace StatisticalRL.EmpiricalBernsteinEntropy

/-- If H and its negative comparator satisfy the two differential
inequalities, the derivative numerator of H/F is nonnegative. -/
theorem ratio_derivative_numerator_nonneg (D H Hd F Fd : ℝ)
    (hD : 0 < D) (hH : H ≤ 0) (hF : F < 0)
    (hHdiff : D*Hd ≤ H) (hFdiff : F ≤ D*Fd) :
    0 ≤ Hd*F-H*Fd := by
  have h₁ : 0 ≤ (D*Hd-H)*F :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hHdiff) hF.le
  have h₂ : 0 ≤ H*(F-D*Fd) :=
    mul_nonneg_of_nonpos_of_nonpos hH (sub_nonpos.mpr hFdiff)
  have h : 0 ≤ D*(Hd*F-H*Fd) := by nlinarith
  nlinarith

/-- The ratio is differentiable with a nonnegative derivative at any positive
point where the two comparison inequalities hold. -/
theorem ratio_has_nonnegative_derivative (H F : ℝ → ℝ) (x Hd Fd D : ℝ)
    (hHderiv : HasDerivAt H Hd x) (hFderiv : HasDerivAt F Fd x)
    (hD : 0 < D) (hH : H x ≤ 0) (hF : F x < 0)
    (hHdiff : D*Hd ≤ H x) (hFdiff : F x ≤ D*Fd) :
    HasDerivAt (fun t ↦ H t/F t) ((Hd*F x-H x*Fd)/(F x)^2) x ∧
      0 ≤ (Hd*F x-H x*Fd)/(F x)^2 := by
  constructor
  · exact hHderiv.div hFderiv (ne_of_lt hF)
  · exact div_nonneg (ratio_derivative_numerator_nonneg D (H x) Hd (F x) Fd
      hD hH hF hHdiff hFdiff) (sq_nonneg _)

end StatisticalRL.EmpiricalBernsteinEntropy

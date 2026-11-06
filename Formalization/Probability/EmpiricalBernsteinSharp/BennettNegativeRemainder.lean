import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Private, uncompiled negative-side component of the exact Bennett MGF.
No probability result is asserted. -/
namespace StatisticalRL.SharpBernstein

/-- The exponential lies below its quadratic Taylor polynomial on the
nonpositive half-line. -/
theorem exp_le_quadratic_of_nonpos (z : ℝ) (hz : z ≤ 0) :
    Real.exp z ≤ 1 + z + z^2 / 2 := by
  let g : ℝ → ℝ := fun x ↦ 1 + x + x^2 / 2 - Real.exp x
  have hd (x : ℝ) : HasDerivAt g (1 + x - Real.exp x) x := by
    dsimp [g]
    convert (((hasDerivAt_id x).const_add 1).add
      (((hasDerivAt_id x).pow 2).div_const 2)).sub (Real.hasDerivAt_exp x) using 1 <;> simp only [id_eq] <;> ring
  have hm : Antitone g := antitone_of_hasDerivAt_nonpos hd (by
    intro x
    have h := Real.add_one_le_exp x
    dsimp
    linarith)
  have h := hm hz
  dsimp [g] at h
  norm_num at h
  linarith

/-- A nonpositive scaled value has no larger exponential remainder than the
positive endpoint coefficient. -/
theorem exp_remainder_scaled_nonpositive (a x : ℝ)
    (ha : 0 ≤ a) (hx : x ≤ 0) :
    Real.exp (a*x) ≤ 1 + a*x + x^2 * (Real.exp a - 1 - a) := by
  have hz : a*x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hx
  have hq := exp_le_quadratic_of_nonpos (a*x) hz
  have haquad := Real.quadratic_le_exp_of_nonneg ha
  have hmul : 0 ≤ x^2 * (Real.exp a - 1 - a - a^2/2) :=
    mul_nonneg (sq_nonneg x) (by linarith)
  nlinarith
end StatisticalRL.SharpBernstein

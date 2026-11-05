import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

/-! scalar ingredient for arbitrary-space conditional Hoeffding.
This is not the Azuma theorem or a probability assumption. -/
namespace StatisticalRL

/-- The exponential lies below its symmetric chord on `[-B,B]`. -/
theorem azuma_exp_symmetric_chord (B x t : ℝ) (hB : 0<B) (hx : |x|≤B) :
    Real.exp (t*x) ≤ Real.cosh (t*B) + (Real.sinh (t*B)/B)*x := by
  have habs : |x/B|≤1 := by
    rw [abs_div, abs_of_pos hB]
    exact (div_le_one hB).2 hx
  have h := Real.exp_mul_le_cosh_add_mul_sinh habs (t*B)
  have hxmul : (x/B)*(t*B)=t*x := by field_simp
  have hcoeff : (x/B)*Real.sinh (t*B) = (Real.sinh (t*B)/B)*x := by ring
  rw [hxmul,hcoeff] at h
  exact h

/-- The zero-width source endpoint forces the increment to vanish. -/
theorem azuma_zero_width (x : ℝ) (hx : |x|≤0) : x=0 := by
  exact abs_eq_zero.mp (le_antisymm hx (abs_nonneg x))

/-- The symmetric chord's constant term has the required Gaussian bound. -/
theorem azuma_cosh_bound (B t : ℝ) :
    Real.cosh (t*B) ≤ Real.exp (t^2*B^2/2) := by
  convert Real.cosh_le_exp_half_sq (t*B) using 1 <;> ring
end StatisticalRL

import Formalization.ModelFree.QLearningPinskerBinary
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Strong convexity of binary negative entropy, including continuity at endpoints. -/

namespace StatisticalRL.QLearning

/-- The quadratic-adjusted binary entropy is continuous even at 0 and 1,
using Mathlib's continuous zero-safe extension of `x log x`. -/
theorem qBinaryStrongPotential_continuous : Continuous qBinaryStrongPotential := by
  have hmul : Continuous (fun x : ℝ ↦ x * Real.log x) := Real.continuous_mul_log
  have hright : Continuous (fun x : ℝ ↦ (1 - x) * Real.log (1 - x)) :=
    hmul.comp (continuous_const.sub continuous_id)
  have hpotential : Continuous qBinaryPotential := by
    simpa [qBinaryPotential] using hmul.add hright
  have hquad : Continuous (fun x : ℝ ↦ 2 * x ^ 2) :=
    continuous_const.mul (continuous_id.pow 2)
  simpa [qBinaryStrongPotential] using hpotential.sub hquad

/-- Interior derivative of the adjusted binary entropy. The reflected
`(1-x) log(1-x)` summand uses the affine chain rule. -/
theorem qBinaryStrongPotential_hasDerivAt {x : ℝ} (hx : 0 < x ∧ x < 1) :
    HasDerivAt qBinaryStrongPotential
      (Real.log x - Real.log (1 - x) - 4 * x) x := by
  have hleft : HasDerivAt (fun y : ℝ ↦ y * Real.log y)
      (Real.log x + 1) x := Real.hasDerivAt_mul_log hx.1.ne'
  have hrightBase : HasDerivAt (fun y : ℝ ↦ y * Real.log y)
      (Real.log (1 - x) + 1) (1 - x) :=
    Real.hasDerivAt_mul_log (ne_of_gt (sub_pos.mpr hx.2))
  have hright := hrightBase.comp_const_sub 1 x
  have hquad : HasDerivAt (fun y : ℝ ↦ 2 * y ^ 2) (2 * (2 * x)) x := by
    convert (hasDerivAt_pow 2 x).const_mul 2 using 1 <;> ring
  have hsum := (hleft.add hright).sub hquad
  convert hsum using 1
  · ring_nf

/-- The interior second derivative equals the nonnegative rational curvature
`(2x−1)^2/(x(1−x))`. -/
theorem qBinaryStrongPotential_hasDerivAt_derivative {x : ℝ}
    (hx : 0 < x ∧ x < 1) :
    HasDerivAt (fun y : ℝ ↦ Real.log y - Real.log (1 - y) - 4 * y)
      (x⁻¹ + (1 - x)⁻¹ - 4) x := by
  have hlogLeft := Real.hasDerivAt_log hx.1.ne'
  have hlogRightBase := Real.hasDerivAt_log (ne_of_gt (sub_pos.mpr hx.2))
  have hlogRight := hlogRightBase.comp_const_sub 1 x
  have hlinear : HasDerivAt (fun y : ℝ ↦ -4 * y) (-4) x :=
    hasDerivAt_const_mul (-4)
  have hsum := (hlogLeft.sub hlogRight).add hlinear
  convert hsum using 1
  · ext y
    simp only [Pi.add_apply, Pi.sub_apply]
    ring_nf
  · ring_nf

/-- The source-specific curvature proof, including the closed endpoints via
continuity. At interior points the denominator is positive, so the exact
curvature is nonnegative. -/
theorem qBinaryStrongPotential_convex :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) qBinaryStrongPotential := by
  let g' : ℝ → ℝ := fun x ↦ Real.log x - Real.log (1 - x) - 4 * x
  let g'' : ℝ → ℝ := fun x ↦ x⁻¹ + (1 - x)⁻¹ - 4
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (D := Set.Icc (0 : ℝ) 1) (f := qBinaryStrongPotential)
    (f' := g') (f'' := g'') (convex_Icc 0 1) ?_ ?_ ?_ ?_
  · exact qBinaryStrongPotential_continuous.continuousOn
  · intro x hx
    have hx' : 0 < x ∧ x < 1 := by simpa [interior_Icc] using hx
    simpa [g'] using (qBinaryStrongPotential_hasDerivAt hx').hasDerivWithinAt
  · intro x hx
    have hx' : 0 < x ∧ x < 1 := by simpa [interior_Icc] using hx
    simpa [g''] using (qBinaryStrongPotential_hasDerivAt_derivative hx').hasDerivWithinAt
  · intro x hx
    have hx' : 0 < x ∧ x < 1 := by simpa [interior_Icc] using hx
    have hden : 0 < x * (1 - x) := mul_pos hx'.1 (sub_pos.mpr hx'.2)
    have hxne : x ≠ 0 := ne_of_gt hx'.1
    have hx1ne : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx'.2)
    have hcurv : g'' x = (2 * x - 1) ^ 2 / (x * (1 - x)) := by
      dsimp [g'']
      field_simp [hxne, hx1ne]
      ring
    rw [hcurv]
    positivity

/-- Fully supplied coefficient-2 binary Pinsker inequality with the source
support conventions: at baseline endpoints absolute continuity forces equality. -/
theorem qBinaryPinsker_source_complete
    (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hsupport₀ : q = 0 → p = 0) (hsupport₁ : q = 1 → p = 1) :
    2 * (p - q) ^ 2 ≤ qBinaryKL p q := by
  apply qBinaryPinsker_of_convex p q hp₀ hp₁ hq₀ hq₁ hsupport₀ hsupport₁
    qBinaryStrongPotential_convex
  intro hqlo hqhi
  exact qBinaryStrongPotential_hasDerivAt ⟨hqlo, hqhi⟩

end StatisticalRL.QLearning

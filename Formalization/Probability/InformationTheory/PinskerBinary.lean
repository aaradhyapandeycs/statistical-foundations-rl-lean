import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Binary Pinsker reduced to strong convexity of binary negative entropy. Boundary probabilities use the zero-safe extension. -/

namespace StatisticalRL.QLearning

/-- Binary negative entropy potential, with Mathlib's totalized `log 0`;
the endpoint products are zero. -/
noncomputable def qBinaryPotential (x : ℝ) : ℝ :=
  x * Real.log x + (1 - x) * Real.log (1 - x)

/-- Potential after subtracting the quadratic whose Bregman divergence is
`2 (p-q)^2`. -/
noncomputable def qBinaryStrongPotential (x : ℝ) : ℝ := qBinaryPotential x - 2 * x ^ 2

/-- Binary KL in Bregman form. At the two baseline endpoints, it is assigned
the only support-compatible value, zero. For `0<q<1`, this equals
`p log(p/q)+(1-p)log((1-p)/(1-q))`, with `0 log 0 = 0`. -/
noncomputable def qBinaryKL (p q : ℝ) : ℝ :=
  if q = 0 then 0 else if q = 1 then 0 else
    qBinaryPotential p - qBinaryPotential q -
      (Real.log q - Real.log (1 - q)) * (p - q)

/-- The coefficient-two Pinsker gap is exactly the Bregman remainder of the
quadratic-adjusted binary entropy at an interior baseline. -/
theorem qBinaryKL_sub_quadratic_eq_strongBregman
    (p q : ℝ) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    qBinaryKL p q - 2 * (p - q) ^ 2 =
      qBinaryStrongPotential p - qBinaryStrongPotential q -
        (Real.log q - Real.log (1 - q) - 4 * q) * (p - q) := by
  unfold qBinaryKL
  rw [if_neg hq0, if_neg hq1]
  unfold qBinaryStrongPotential
  ring

/-- Exact binary Pinsker inequality from convexity of the quadratic-adjusted
binary entropy. This isolates the calculus fact from the zero-support
boundary handling. -/
theorem qBinaryPinsker_interior_of_convex
    (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 < q) (hq₁ : q < 1)
    (hconv : ConvexOn ℝ (Set.Icc 0 1) qBinaryStrongPotential)
    (hderiv : HasDerivAt qBinaryStrongPotential
      (Real.log q - Real.log (1 - q) - 4 * q) q) :
    2 * (p - q) ^ 2 ≤ qBinaryKL p q := by
  have hp : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp₀, hp₁⟩
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq₀.le, hq₁.le⟩
  have hq0 : q ≠ 0 := ne_of_gt hq₀
  have hq1 : q ≠ 1 := ne_of_lt hq₁
  have hderiv' : deriv qBinaryStrongPotential q =
      Real.log q - Real.log (1 - q) - 4 * q := hderiv.deriv
  by_cases hpq : p = q
  · subst p
    simp [qBinaryKL, hq0, hq1, qBinaryPotential, qBinaryStrongPotential]
  · rcases lt_or_gt_of_ne hpq with hpq' | hpq'
    · have hs := hconv.slope_le_deriv hp hq hpq' hderiv.differentiableAt
      rw [hderiv'] at hs
      have hs' : qBinaryStrongPotential q - qBinaryStrongPotential p ≤
          (Real.log q - Real.log (1 - q) - 4 * q) * (q - p) := by
        have hdef := slope_def_field qBinaryStrongPotential p q
        rw [hdef] at hs
        have hpos : q - p ≠ 0 := ne_of_gt (sub_pos.mpr hpq')
        have hmul := (div_le_iff₀ (sub_pos.mpr hpq')).mp hs
        nlinarith
      have hbreg : 0 ≤ qBinaryStrongPotential p - qBinaryStrongPotential q -
          (Real.log q - Real.log (1 - q) - 4 * q) * (p - q) := by
        linarith
      have hid := qBinaryKL_sub_quadratic_eq_strongBregman p q hq0 hq1
      rw [qBinaryKL, if_neg hq0, if_neg hq1] at hid
      have hresult : 2 * (p - q) ^ 2 ≤ qBinaryKL p q := by
        rw [qBinaryKL, if_neg hq0, if_neg hq1]
        linarith
      exact hresult
    · have hs := hconv.deriv_le_slope hq hp hpq' hderiv.differentiableAt
      rw [hderiv'] at hs
      have hs' : (Real.log q - Real.log (1 - q) - 4 * q) * (p - q) ≤
          qBinaryStrongPotential p - qBinaryStrongPotential q := by
        have hdef := slope_def_field qBinaryStrongPotential q p
        rw [hdef] at hs
        have hpos : p - q ≠ 0 := ne_of_gt (sub_pos.mpr hpq')
        have hmul := (le_div_iff₀ (sub_pos.mpr hpq')).mp hs
        nlinarith
      have hbreg : 0 ≤ qBinaryStrongPotential p - qBinaryStrongPotential q -
          (Real.log q - Real.log (1 - q) - 4 * q) * (p - q) := by
        linarith
      have hid := qBinaryKL_sub_quadratic_eq_strongBregman p q hq0 hq1
      rw [qBinaryKL, if_neg hq0, if_neg hq1] at hid
      have hresult : 2 * (p - q) ^ 2 ≤ qBinaryKL p q := by
        rw [qBinaryKL, if_neg hq0, if_neg hq1]
        linarith
      exact hresult

/-- Boundary-safe binary Pinsker. Absolute continuity of the binary laws is
expressed by `q=0→p=0` and `q=1→p=1`; no division by a zero baseline atom
is performed. -/
theorem qBinaryPinsker_of_convex
    (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hsupport₀ : q = 0 → p = 0) (hsupport₁ : q = 1 → p = 1)
    (hconv : ConvexOn ℝ (Set.Icc 0 1) qBinaryStrongPotential)
    (hderiv : 0 < q → q < 1 → HasDerivAt qBinaryStrongPotential
      (Real.log q - Real.log (1 - q) - 4 * q) q) :
    2 * (p - q) ^ 2 ≤ qBinaryKL p q := by
  by_cases hq0 : q = 0
  · have hp : p = q := (hsupport₀ hq0).trans hq0.symm
    subst p
    simp [qBinaryKL, hq0]
  by_cases hq1 : q = 1
  · have hp : p = q := (hsupport₁ hq1).trans hq1.symm
    subst p
    simp [qBinaryKL, hq0, hq1]
  have hqpos : 0 < q := lt_of_le_of_ne hq₀ (Ne.symm hq0)
  have hqlt : q < 1 := lt_of_le_of_ne hq₁ hq1
  exact qBinaryPinsker_interior_of_convex p q hp₀ hp₁ hqpos hqlt hconv
    (hderiv hqpos hqlt)

end StatisticalRL.QLearning

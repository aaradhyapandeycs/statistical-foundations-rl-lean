import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The Gaussian shift identity (Remark 5.12)

`∫⁻ φ(y + c) dN(0,1)(y) = ∫⁻ φ(y) e^{cy − c²/2} dN(0,1)(y)`, and its version for one coordinate of
a standard Gaussian vector.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace StatisticalRL.GaussianBanditLB

/-- One-dimensional Gaussian shift (discrete Cameron–Martin). -/
theorem lintegral_gaussian_shift (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (c : ℝ) :
    ∫⁻ y, φ (y + c) ∂gaussianReal 0 1 =
      ∫⁻ y, φ y * ENNReal.ofReal (Real.exp (c * y - c ^ 2 / 2)) ∂gaussianReal 0 1 := by
  rw [← lintegral_map hφ (measurable_add_const c), gaussianReal_map_add_const,
    gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hφ,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _)
      (hφ.mul (by fun_prop))]
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply, gaussianPDF_def]
  rw [mul_comm (φ y), ← mul_assoc, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 2
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, zero_add, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

variable {A : ℕ}

/-- Gaussian shift of one coordinate of a standard Gaussian vector. -/
theorem lintegral_coord_shift (b : Fin A) (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (c : ℝ) :
    ∫⁻ y, φ (y b + c) ∂(Measure.pi fun _ : Fin A => gaussianReal 0 1) =
      ∫⁻ y, φ (y b) * ENNReal.ofReal (Real.exp (c * y b - c ^ 2 / 2))
        ∂(Measure.pi fun _ : Fin A => gaussianReal 0 1) := by
  have hmp := measurePreserving_eval (μ := fun _ : Fin A => gaussianReal 0 1) b
  rw [hmp.lintegral_comp (f := fun x => φ (x + c)) (hφ.comp (measurable_add_const c)),
    hmp.lintegral_comp (f := fun x => φ x * ENNReal.ofReal (Real.exp (c * x - c ^ 2 / 2)))
      (hφ.mul (by fun_prop))]
  exact lintegral_gaussian_shift φ hφ c

/-- One coordinate of a standard Gaussian vector is integrable. -/
theorem integrable_coord (b : Fin A) :
    Integrable (fun y : Fin A → ℝ => y b) (Measure.pi fun _ : Fin A => gaussianReal 0 1) :=
  integrable_comp_eval (i := b) (f := id) ((memLp_id_gaussianReal 1).integrable le_rfl)

/-- One coordinate of a standard Gaussian vector has mean zero. -/
theorem integral_coord (b : Fin A) :
    ∫ y, y b ∂(Measure.pi fun _ : Fin A => gaussianReal 0 1) = 0 := by
  have := integral_comp_eval (μ := fun _ : Fin A => gaussianReal 0 1) (i := b) (f := id)
    aestronglyMeasurable_id
  simp only [id] at this
  rw [this, integral_id_gaussianReal]

end StatisticalRL.GaussianBanditLB

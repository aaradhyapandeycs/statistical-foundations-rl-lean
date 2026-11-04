import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-! General probability-space square-variance bounds with coefficient four. -/
namespace StatisticalRL.GeneralVariance
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded measurable Y whose square is controlled by the centered square
of X has correspondingly controlled variance. The boundedness inputs below
are proved for the two concrete Y choices in the source-facing theorems. -/
private theorem centered_variance_control
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (C : ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hcenter : ∀ ω, |X ω - ∫ z, X z ∂μ| ≤ 2*C)
    (hYbound : ∀ ω, |Y ω| ≤ 4*C^2)
    (hpoint : ∀ ω, (Y ω)^2 ≤ 4*C^2 * (X ω - ∫ z, X z ∂μ)^2) :
    ProbabilityTheory.variance Y μ ≤ 4*C^2 * ProbabilityTheory.variance X μ := by
  let Z : Ω → ℝ := fun ω => X ω - ∫ z, X z ∂μ
  have hZmeas : Measurable Z := by dsimp [Z]; fun_prop
  have hZ2 : MemLp Z 2 μ := MemLp.of_bound hZmeas.aestronglyMeasurable (2*C)
    (Filter.Eventually.of_forall (fun ω => by simpa [Z, Real.norm_eq_abs] using hcenter ω))
  have hY2 : MemLp Y 2 μ := MemLp.of_bound hY.aestronglyMeasurable (4*C^2)
    (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hYbound ω))
  have hleft : Integrable (fun ω => Y ω ^ 2) μ := hY2.integrable_sq
  have hright : Integrable (fun ω => 4*C^2 * Z ω ^ 2) μ := hZ2.integrable_sq.const_mul _
  calc
    ProbabilityTheory.variance Y μ ≤ ∫ ω, Y ω^2 ∂μ := by
      simpa only [Pi.pow_apply] using ProbabilityTheory.variance_le_expectation_sq hY.aestronglyMeasurable
    _ ≤ ∫ ω, 4*C^2 * Z ω^2 ∂μ :=
      integral_mono hleft hright (fun ω => by simpa [Z] using hpoint ω)
    _ = 4*C^2 * ProbabilityTheory.variance X μ := by
      rw [integral_const_mul, ProbabilityTheory.variance_eq_integral hX.aemeasurable]

/-- Corrected signed-variable square variance: first source inequality. -/
theorem variance_square_le_four_of_abs_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (C : ℝ) (hbound : ∀ ω, |X ω| ≤ C) :
    ProbabilityTheory.variance (fun ω => (X ω)^2) μ ≤
      4*C^2 * ProbabilityTheory.variance X μ := by
  let m : ℝ := ∫ ω, X ω ∂μ
  have hm : |m| ≤ C := by
    have hb := norm_integral_le_of_norm_le_const (μ := μ) (f := X) (C := C)
      (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hbound ω))
    simpa [m, Real.norm_eq_abs, probReal_univ] using hb
  have hC : 0 ≤ C := (abs_nonneg m).trans hm
  have hminus (ω : Ω) : |X ω - m| ≤ 2*C := by
    calc
      _ ≤ |X ω| + |m| := abs_sub _ _
      _ ≤ C + C := add_le_add (hbound ω) hm
      _ = 2*C := by ring
  have hplus (ω : Ω) : |X ω + m| ≤ 2*C := by
    calc
      _ ≤ |X ω| + |m| := abs_add_le _ _
      _ ≤ C + C := add_le_add (hbound ω) hm
      _ = 2*C := by ring
  let Y : Ω → ℝ := fun ω => (X ω)^2 - m^2
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hYbound (ω : Ω) : |Y ω| ≤ 4*C^2 := by
    have hp := mul_le_mul (hminus ω) (hplus ω) (abs_nonneg _) (by positivity : 0 ≤ 2*C)
    have heq : |Y ω| = |X ω - m| * |X ω + m| := by
      dsimp [Y]
      rw [← abs_mul]
      congr 1
      ring
    rw [heq]
    nlinarith only [hp]
  have hpoint (ω : Ω) : (Y ω)^2 ≤ 4*C^2 * (X ω - m)^2 := by
    have ha := abs_le.mp (hplus ω)
    have hs : (X ω + m)^2 ≤ (2*C)^2 := by nlinarith only [ha.1, ha.2, hC]
    have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg (X ω - m))
    dsimp [Y]
    nlinarith only [hmul]
  have haux := centered_variance_control μ X Y C hX hY (by simpa [m] using hminus)
    hYbound (by simpa [m] using hpoint)
  have hshift := ProbabilityTheory.variance_sub_const (μ := μ) ((hX.pow_const 2).aestronglyMeasurable) (m^2)
  change ProbabilityTheory.variance Y μ = ProbabilityTheory.variance (fun ω => X ω ^ 2) μ at hshift
  rw [← hshift]
  exact haux

/-- Corrected signed-variable centered-square variance, with coefficient 4.
This general probability-space statement includes zero variance and C=0. -/
theorem variance_centeredSquare_le_four_of_abs_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (C : ℝ) (hbound : ∀ ω, |X ω| ≤ C) :
    ProbabilityTheory.variance (fun ω => (X ω - ∫ z, X z ∂μ)^2) μ ≤
      4*C^2 * ProbabilityTheory.variance X μ := by
  let m : ℝ := ∫ ω, X ω ∂μ
  have hm : |m| ≤ C := by
    have hb := norm_integral_le_of_norm_le_const (μ := μ) (f := X) (C := C)
      (Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hbound ω))
    simpa [m, Real.norm_eq_abs, probReal_univ] using hb
  have hC : 0 ≤ C := (abs_nonneg m).trans hm
  have hminus (ω : Ω) : |X ω - m| ≤ 2*C := by
    calc
      _ ≤ |X ω| + |m| := abs_sub _ _
      _ ≤ C + C := add_le_add (hbound ω) hm
      _ = 2*C := by ring
  have hs (ω : Ω) : (X ω - m)^2 ≤ 4*C^2 := by
    have ha := abs_le.mp (hminus ω)
    nlinarith only [ha.1, ha.2, hC]
  let Y : Ω → ℝ := fun ω => (X ω - m)^2
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hYbound (ω : Ω) : |Y ω| ≤ 4*C^2 := by
    simpa only [Y, abs_of_nonneg (sq_nonneg (X ω - m))] using hs ω
  have hpoint (ω : Ω) : (Y ω)^2 ≤ 4*C^2 * (X ω - m)^2 := by
    have hmul := mul_le_mul_of_nonneg_left (hs ω) (sq_nonneg (X ω - m))
    dsimp [Y]
    nlinarith only [hmul]
  simpa [Y, m] using centered_variance_control μ X Y C hX hY (by simpa [m] using hminus)
    hYbound (by simpa [m] using hpoint)
end StatisticalRL.GeneralVariance

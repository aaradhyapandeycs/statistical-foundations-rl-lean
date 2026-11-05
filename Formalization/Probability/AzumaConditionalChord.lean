import Formalization.Probability.AzumaScalarChord
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! arbitrary-space conditional exponential-moment ingredient.
No kernel, standard-Borel hypothesis, martingale bound, or source theorem is asserted. -/
namespace StatisticalRL
open MeasureTheory ProbabilityTheory

theorem azuma_condExp_exp_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m≤mΩ) (X : Ω → ℝ)
    (hX : @Measurable Ω ℝ mΩ (inferInstance : MeasurableSpace ℝ) X)
    (B : ℝ) (hB : 0≤B) (hbound : ∀ ω, |X ω|≤B)
    (hcenter : μ[X | m] =ᵐ[μ] 0) (t : ℝ) :
    μ[(fun ω => Real.exp (t*X ω)) | m] ≤ᵐ[μ]
      (fun _ => Real.exp (t^2*B^2/2)) := by
  by_cases hz : B=0
  · subst B
    have hx0 : X = 0 := by
      funext ω
      exact azuma_zero_width (X ω) (hbound ω)
    have heq : (fun ω => Real.exp (t*X ω)) = (fun _ => (1 : ℝ)) := by simp [hx0]
    rw [heq, condExp_const hm]
    filter_upwards [] with ω
    simp
  · have hBp : 0<B := lt_of_le_of_ne hB (Ne.symm hz)
    have hIcc : ∀ ω, X ω ∈ Set.Icc (-B) B := by
      intro ω
      exact abs_le.mp (hbound ω)
    have hXi : Integrable X μ := Integrable.of_mem_Icc (-B) B hX.aemeasurable
      (Filter.Eventually.of_forall hIcc)
    have hEi : Integrable (fun ω => Real.exp (t*X ω)) μ :=
      integrable_exp_mul_of_mem_Icc hX.aemeasurable (Filter.Eventually.of_forall hIcc)
    let c := Real.sinh (t*B)/B
    let g : Ω → ℝ := fun ω => Real.cosh (t*B)+c*X ω
    have hg : Integrable g μ := by
      dsimp [g]
      exact (integrable_const (c := Real.cosh (t*B))).add (hXi.const_mul c)
    have hmono := condExp_mono (m := m) hEi hg (Filter.Eventually.of_forall (fun ω =>
      azuma_exp_symmetric_chord B (X ω) t hBp (hbound ω)))
    have hadd := condExp_add (integrable_const (c := Real.cosh (t*B))) (hXi.const_mul c) m
    have hmul := condExp_smul (μ := μ) (m₀ := mΩ) c X m
    filter_upwards [hmono,hadd,hmul,hcenter] with ω hle hsum hmul' hzero
    have hgzero : μ[g | m] ω = Real.cosh (t*B) := by
      have heqfun : (fun x => c*X x) = c • X := by funext x; rfl
      rw [heqfun] at hsum
      change μ[(fun _ => Real.cosh (t*B)) + c • X | m] ω = Real.cosh (t*B)
      rw [hsum, condExp_const hm]
      simp only [Pi.add_apply]
      rw [hmul']
      simp [hzero]
    exact hle.trans (by rw [hgzero]; exact azuma_cosh_bound B t)
end StatisticalRL

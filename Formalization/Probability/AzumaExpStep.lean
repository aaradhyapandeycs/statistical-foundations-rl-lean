import Formalization.Probability.AzumaConditionalChord
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic

/-! arbitrary-space one-step exponential-moment induction. -/
namespace StatisticalRL
open MeasureTheory ProbabilityTheory

theorem azuma_exp_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m≤mΩ) (S X : Ω → ℝ)
    (hSm : StronglyMeasurable[m] S) (hX : @Measurable Ω ℝ mΩ (inferInstance : MeasurableSpace ℝ) X)
    (C B : ℝ) (hC : 0≤C) (hB : 0≤B)
    (hSbound : ∀ω, |S ω|≤C) (hXbound : ∀ω, |X ω|≤B)
    (hcenter : μ[X | m] =ᵐ[μ] 0) (t : ℝ) :
    (∫ ω, Real.exp (t*(S ω+X ω)) ∂μ) ≤
      Real.exp (t^2*B^2/2) * (∫ ω, Real.exp (t*S ω) ∂μ) := by
  let f : Ω → ℝ := fun ω => Real.exp (t*S ω)
  let g : Ω → ℝ := fun ω => Real.exp (t*X ω)
  have hS : @Measurable Ω ℝ mΩ (inferInstance : MeasurableSpace ℝ) S := (hSm.mono hm).measurable
  have hsIcc : ∀ω, S ω ∈ Set.Icc (-C) C := fun ω => abs_le.mp (hSbound ω)
  have hxIcc : ∀ω, X ω ∈ Set.Icc (-B) B := fun ω => abs_le.mp (hXbound ω)
  have hsumIcc : ∀ω, S ω+X ω ∈ Set.Icc (-(C+B)) (C+B) := by
    intro ω
    have hs := hsIcc ω
    have hx := hxIcc ω
    constructor <;> linarith [hs.1,hs.2,hx.1,hx.2]
  have hf : Integrable f μ := integrable_exp_mul_of_mem_Icc hS.aemeasurable (Filter.Eventually.of_forall hsIcc)
  have hg : Integrable g μ := integrable_exp_mul_of_mem_Icc hX.aemeasurable (Filter.Eventually.of_forall hxIcc)
  have hfg : Integrable (f*g) μ := by
    have hi := integrable_exp_mul_of_mem_Icc (μ := μ) (hS.add hX).aemeasurable (Filter.Eventually.of_forall hsumIcc) (t := t)
    convert hi using 1
    funext ω
    simp only [Pi.mul_apply, f, g, ← Real.exp_add]
    congr 1
    ring
  have hfstrong : StronglyMeasurable[m] f := by
    dsimp [f]
    exact (Real.continuous_exp.comp_stronglyMeasurable (hSm.const_mul t))
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := μ) hfstrong hfg hg
  have hcond := @azuma_condExp_exp_le Ω mΩ μ _ m hm X hX B hB hXbound hcenter t
  have hupper : μ[f*g | m] ≤ᵐ[μ] (fun ω => f ω*Real.exp (t^2*B^2/2)) := by
    filter_upwards [hpull,hcond] with ω heq hle
    rw [heq]
    exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
  have hu : Integrable (fun ω => f ω*Real.exp (t^2*B^2/2)) μ := hf.mul_const _
  have hint := integral_mono_ae (integrable_condExp (μ := μ) (m := m)) hu hupper
  rw [integral_condExp hm] at hint
  have heq : f*g = (fun ω => Real.exp (t*(S ω+X ω))) := by
    funext ω
    simp only [Pi.mul_apply, f, g, ← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_mul_const] at hint
  simpa only [mul_comm] using hint
end StatisticalRL

import Mathlib.Probability.Moments.SubGaussian

/-! probability helper for the T4 episode concentration step.
Its hypotheses must be proved for the actual episode increment before use;
this lemma alone does not establish a source regret bound. -/
namespace StatisticalRL
open MeasureTheory ProbabilityTheory

/-- Conditional Hoeffding from an actual conditional-mean identity and a
pointwise interval bound. The conditional kernel is Mathlib's conditional
expectation kernel for the same measure and sub-sigma-field. -/
theorem hasCondSubgaussianMGF_of_pointwise_Icc_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X : Ω → ℝ) (hX : @Measurable Ω ℝ mΩ (inferInstance : MeasurableSpace ℝ) X) (a b : ℝ)
    (hbound : ∀ ω, X ω ∈ Set.Icc a b)
    (hcenter : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2)^2) μ := by
  letI : MeasurableSpace Ω := mΩ
  have hInt : Integrable X μ :=
    Integrable.of_mem_Icc a b (hX.aemeasurable (μ := μ)) (Filter.Eventually.of_forall hbound)
  have htrim : μ[X | m] =ᵐ[μ.trim hm] 0 :=
    ae_eq_trim_of_measurable hm stronglyMeasurable_condExp.measurable
      measurable_const hcenter
  have hkernel := condExp_ae_eq_trim_integral_condExpKernel hm hInt
  change Kernel.HasSubgaussianMGF X ((‖b - a‖₊ / 2)^2)
    (condExpKernel μ m) (μ.trim hm)
  constructor
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hX.aemeasurable
      (Filter.Eventually.of_forall hbound)
  · filter_upwards [htrim, hkernel] with ω hzero heq
    have hmean : ∫ y, X y ∂condExpKernel μ m ω = 0 := heq.symm.trans hzero
    exact (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hX.aemeasurable
      (Filter.Eventually.of_forall hbound) hmean).mgf_le

end StatisticalRL

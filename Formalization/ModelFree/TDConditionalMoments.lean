import Formalization.ModelFree.TDCausality
import Formalization.ModelFree.TDActualErrorDecomposition
import Formalization.Probability.Variance
import Formalization.Probability.EmpiricalRow
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! Actual conditional moments of the predictable TD policy-row fluctuation.
Fresh source update t+1 is conditioned on used source times1,…,t. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdMomentsStateMeasurable : MeasurableSpace State := ⊤

noncomputable def tdValueBefore (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (data : TDSamples State T) : State → ℝ :=
  tdIterate M π η (tdSamplesExtend M T data) V₀ t

noncomputable def tdRowMean (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (s : State) (v : State → ℝ) : ℝ := (M.policyTransition π s).expectation v

noncomputable def tdRowIncrement (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t < T) (V₀ : State → ℝ) (s : State)
    (data : TDSamples State T) : ℝ :=
  tdValueBefore M π η T t V₀ data (data (s,⟨t+1,by omega⟩)) -
    tdRowMean M π s (tdValueBefore M π η T t V₀ data)

noncomputable def tdFreshIndicator (T t : ℕ) (ht : t < T) (s x : State)
    (data : TDSamples State T) : ℝ := by
  classical
  exact if data (s,⟨t+1,by omega⟩) = x then 1 else 0

noncomputable def tdFreshSigma (T t : ℕ) (ht : t < T) (s : State) : MeasurableSpace (TDSamples State T) :=
  MeasurableSpace.comap (fun data : TDSamples State T ↦ data (s,⟨t+1,by omega⟩)) inferInstance

theorem tdSampling_integrable (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (T : ℕ) (f : TDSamples State T → ℝ) : Integrable f (tdSamplingLaw M π T) := Integrable.of_finite

theorem tdPastSigma_le (T t : ℕ) : tdPastSigma (State := State) T t ≤
    (inferInstance : MeasurableSpace (TDSamples State T)) :=
  (measurable_of_countable (tdPastData (State := State) T t)).comap_le

theorem tdValueBefore_stronglyMeasurable (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ) (x : State) :
    StronglyMeasurable[tdPastSigma T t] (fun data ↦ tdValueBefore M π η T t V₀ data x) :=
  ((measurable_pi_apply x).comp (tdIterate_measurable_past M π η T t ht V₀)).stronglyMeasurable

omit [Fintype State] in
theorem tdFreshSigma_le (T t : ℕ) (ht : t < T) (s : State) :
    tdFreshSigma T t ht s ≤ (inferInstance : MeasurableSpace (TDSamples State T)) :=
  (measurable_pi_apply (s,(⟨t+1,by omega⟩ : Fin (T+1)))).comap_le

theorem tdFreshSigma_indep_past (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (T t : ℕ) (ht : t < T) (s : State) :
    Indep (tdFreshSigma T t ht s) (tdPastSigma T t) (tdSamplingLaw M π T) := by
  simpa [tdFreshSigma, tdPastSigma, IndepFun_iff_Indep] using (tdPast_indep_fresh M π T t ht s).symm

theorem tdFreshIndicator_strong (T t : ℕ) (ht : t < T) (s x : State) :
    StronglyMeasurable[tdFreshSigma T t ht s] (tdFreshIndicator T t ht s x) := by
  classical
  let f : State → ℝ := fun y ↦ if y = x then 1 else 0
  have hf : Measurable f := measurable_of_countable _
  exact (hf.comp (comap_measurable (fun data : TDSamples State T ↦
    data (s,(⟨t+1,by omega⟩ : Fin (T+1)))))).stronglyMeasurable

theorem tdFreshIndicator_integral (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (T t : ℕ) (ht : t < T) (s x : State) :
    ∫ data, tdFreshIndicator T t ht s x data ∂tdSamplingLaw M π T = (M.policyTransition π s).prob x := by
  classical
  let v : State → ℝ := fun y ↦ if y = x then 1 else 0
  have hmap := tdFresh_marginal M π T t ht s
  have hv : Integrable v ((tdSamplingLaw M π T).map
      (fun data : TDSamples State T ↦ data (s,(⟨t+1,by omega⟩ : Fin (T+1))))) := Integrable.of_finite
  have h := integral_map (μ := tdSamplingLaw M π T)
    (measurable_pi_apply (s,(⟨t+1,by omega⟩ : Fin (T+1)))).aemeasurable hv.aestronglyMeasurable
  rw [hmap, FiniteDistribution.rowMeasure_integral] at h
  simpa [v, tdFreshIndicator, FiniteDistribution.expectation] using h.symm

theorem tdFreshIndicator_condExp (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (T t : ℕ) (ht : t < T) (s x : State) :
    (tdSamplingLaw M π T)[tdFreshIndicator T t ht s x | tdPastSigma T t] =ᵐ[tdSamplingLaw M π T]
      fun _ ↦ (M.policyTransition π s).prob x := by
  have h := condExp_indep_eq (tdFreshSigma_le T t ht s) (tdPastSigma_le T t)
    (tdFreshIndicator_strong T t ht s x) (tdFreshSigma_indep_past M π T t ht s)
  filter_upwards [h] with data hd
  simpa only [tdFreshIndicator_integral M π T t ht s x] using hd

theorem tdFresh_predictable_sum_condExp (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (T t : ℕ) (ht : t < T) (s : State) (c : State → TDSamples State T → ℝ)
    (hc : ∀ x, StronglyMeasurable[tdPastSigma T t] (c x)) :
    (tdSamplingLaw M π T)[∑ x, c x * tdFreshIndicator T t ht s x | tdPastSigma T t]
      =ᵐ[tdSamplingLaw M π T] ∑ x, fun data ↦ c x data * (M.policyTransition π s).prob x := by
  classical
  have hsum := condExp_finset_sum (μ := tdSamplingLaw M π T) (s := Finset.univ)
    (f := fun x ↦ c x * tdFreshIndicator T t ht s x)
    (fun x hx ↦ tdSampling_integrable M π T _) (tdPastSigma T t)
  filter_upwards [hsum, ae_all_iff.mpr (fun x ↦
    (condExp_mul_of_stronglyMeasurable_left (hc x) (tdSampling_integrable M π T _)
      (tdSampling_integrable M π T _)).trans
      ((Filter.EventuallyEq.refl _ _).mul (tdFreshIndicator_condExp M π T t ht s x)))] with data hd hterms
  rw [hd]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun x hx ↦ hterms x)

theorem tdRowMean_stronglyMeasurable (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ) (s : State) :
    StronglyMeasurable[tdPastSigma T t] (fun data ↦ tdRowMean M π s (tdValueBefore M π η T t V₀ data)) := by
  classical
  unfold tdRowMean FiniteDistribution.expectation
  exact Finset.stronglyMeasurable_fun_sum _ fun x hx ↦
    stronglyMeasurable_const.mul (tdValueBefore_stronglyMeasurable M π η T t ht V₀ x)

theorem tdFresh_value_condExp (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t < T) (V₀ : State → ℝ) (s : State) :
    (tdSamplingLaw M π T)[(fun data ↦ tdValueBefore M π η T t V₀ data
      (data (s,⟨t+1,by omega⟩))) | tdPastSigma T t] =ᵐ[tdSamplingLaw M π T]
      fun data ↦ tdRowMean M π s (tdValueBefore M π η T t V₀ data) := by
  classical
  have he : (fun data : TDSamples State T ↦ tdValueBefore M π η T t V₀ data (data (s,⟨t+1,by omega⟩))) =
      ∑ x, (fun data ↦ tdValueBefore M π η T t V₀ data x) * tdFreshIndicator T t ht s x := by
    funext data
    simp [tdFreshIndicator]
  rw [he]
  have h := tdFresh_predictable_sum_condExp M π T t ht s
    (fun x data ↦ tdValueBefore M π η T t V₀ data x)
    (fun x ↦ tdValueBefore_stronglyMeasurable M π η T t ht.le V₀ x)
  filter_upwards [h] with data hd
  simpa [tdRowMean, FiniteDistribution.expectation, Finset.sum_apply, mul_comm] using hd

theorem tdRowIncrement_condExp_zero (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t < T) (V₀ : State → ℝ) (s : State) :
    (tdSamplingLaw M π T)[tdRowIncrement M π η T t ht V₀ s | tdPastSigma T t]
      =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
  let f : TDSamples State T → ℝ := fun data ↦ tdValueBefore M π η T t V₀ data (data (s,⟨t+1,by omega⟩))
  let g : TDSamples State T → ℝ := fun data ↦ tdRowMean M π s (tdValueBefore M π η T t V₀ data)
  have hg : (tdSamplingLaw M π T)[g | tdPastSigma T t] = g :=
    condExp_of_stronglyMeasurable (tdPastSigma_le T t)
      (tdRowMean_stronglyMeasurable M π η T t ht.le V₀ s) (tdSampling_integrable M π T g)
  have h := condExp_sub (tdSampling_integrable M π T f) (tdSampling_integrable M π T g) (tdPastSigma T t)
  change (tdSamplingLaw M π T)[f - g | tdPastSigma T t] =ᵐ[tdSamplingLaw M π T] _
  filter_upwards [h, tdFresh_value_condExp M π η T t ht V₀ s] with data hd hv
  change (tdSamplingLaw M π T)[f | tdPastSigma T t] data = g data at hv
  rw [hg] at hd
  simpa only [Pi.sub_apply, hv, sub_self] using hd

theorem tdRowIncrement_condExp_sq (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t < T) (V₀ : State → ℝ) (s : State) :
    (tdSamplingLaw M π T)[(fun data ↦ tdRowIncrement M π η T t ht V₀ s data ^ 2) | tdPastSigma T t]
      =ᵐ[tdSamplingLaw M π T] fun data ↦
        (M.policyTransition π s).variance (tdValueBefore M π η T t V₀ data) := by
  classical
  let c : State → TDSamples State T → ℝ := fun x data ↦
    (tdValueBefore M π η T t V₀ data x - tdRowMean M π s (tdValueBefore M π η T t V₀ data)) ^ 2
  have hc : ∀ x, StronglyMeasurable[tdPastSigma T t] (c x) := by
    intro x
    exact ((tdValueBefore_stronglyMeasurable M π η T t ht.le V₀ x).sub
      (tdRowMean_stronglyMeasurable M π η T t ht.le V₀ s)).pow 2
  have he : (fun data : TDSamples State T ↦ tdRowIncrement M π η T t ht V₀ s data ^ 2) =
      ∑ x, c x * tdFreshIndicator T t ht s x := by
    funext data
    simp [c, tdRowIncrement, tdFreshIndicator]
  rw [he]
  have h := tdFresh_predictable_sum_condExp M π T t ht s c hc
  filter_upwards [h] with data hd
  rw [FiniteDistribution.variance_eq_expectation_centered_sq]
  simpa [c, tdRowMean, FiniteDistribution.expectation, Finset.sum_apply, mul_comm] using hd

/-- The finite-experiment increment is exactly the source error decomposition's
raw innovation at source time t+1, with the same sampled array and old iterate. -/
theorem tdRowIncrement_eq_centeredRowNoise (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t < T) (V₀ : State → ℝ) (s : State) :
    tdRowIncrement M π η T t ht V₀ s = fun data : TDSamples State T ↦
      tdCenteredRowNoise M π η (tdSamplesExtend M T data) V₀ (t + 1) s := by
  funext data
  simp only [tdRowIncrement, tdValueBefore, tdRowMean, tdCenteredRowNoise,
    tdSamplesExtend, dif_pos (by omega : t + 1 < T + 1)]

end StatisticalRL.TemporalDifference

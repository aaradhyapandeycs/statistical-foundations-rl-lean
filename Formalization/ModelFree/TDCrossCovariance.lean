import Formalization.ModelFree.TDConditionalMoments
import Mathlib.Probability.Independence.Integration

/-! TD cross-state conditional-covariance development.
The finite indicator identities below assume no martingale or conditional
independence conclusion. The conditional bridge is derived from the actual product law. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdCrossStateMeasurable : MeasurableSpace State := ⊤

/-- Actual synchronous row noises, evaluated on the same old iterate and
same source-time layer. Distinct states identify distinct product coordinates. -/
noncomputable def tdCrossRowNoise (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T k : ℕ) (hk : k < T)
    (V₀ : State → ℝ) (s r : State) (data : TDSamples State T) : ℝ :=
  tdRowIncrement M π η T k hk V₀ s data * tdRowIncrement M π η T k hk V₀ r data

/-- The product of centered actual noises has an exact double-indicator
expansion. Coefficients are functions of the predictable OLD iterate. -/
theorem tdCrossRowNoise_indicator_expansion (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T k : ℕ) (hk : k < T)
    (V₀ : State → ℝ) (s r : State) (data : TDSamples State T) :
    tdCrossRowNoise M π η T k hk V₀ s r data =
      ∑ x, ∑ y, (tdValueBefore M π η T k V₀ data x - tdRowMean M π s (tdValueBefore M π η T k V₀ data)) *
        (tdValueBefore M π η T k V₀ data y - tdRowMean M π r (tdValueBefore M π η T k V₀ data)) *
        (tdFreshIndicator T k hk s x data * tdFreshIndicator T k hk r y data) := by
  classical
  simp [tdCrossRowNoise, tdRowIncrement, tdFreshIndicator]

/-- The deterministic conditional coefficient sum vanishes exactly, including
zero-probability atoms and arbitrary real predictable values. -/
theorem td_centered_product_sum_eq_zero (p q : FiniteDistribution State) (V : State → ℝ) :
    (∑ x, ∑ y, (V x - p.expectation V) * (V y - q.expectation V) * (p.prob x * q.prob y)) = 0 := by
  have hp : ∑ x, p.prob x * (V x - p.expectation V) = 0 := by
    change p.expectation (fun x ↦ V x - p.expectation V) = 0
    rw [p.expectation_sub, p.expectation_const]
    ring
  have hq : ∑ y, q.prob y * (V y - q.expectation V) = 0 := by
    change q.expectation (fun y ↦ V y - q.expectation V) = 0
    rw [q.expectation_sub, q.expectation_const]
    ring
  calc
    _ = (∑ x, p.prob x * (V x - p.expectation V)) *
        (∑ y, q.prob y * (V y - q.expectation V)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = 0 := by rw [hp, hq]; ring

/-- Sigma-algebra of the entire fresh source-time layer k+1. -/
noncomputable def tdLayerSigma (T k : ℕ) : MeasurableSpace (TDSamples State T) :=
  MeasurableSpace.comap (tdLayerData (State := State) T k) inferInstance

theorem tdLayerSigma_le (T k : ℕ) : tdLayerSigma (State := State) T k ≤
    (inferInstance : MeasurableSpace (TDSamples State T)) :=
  (measurable_of_countable (tdLayerData (State := State) T k)).comap_le

theorem tdLayerSigma_indep_past (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (T k : ℕ) : Indep (tdLayerSigma (State := State) T k) (tdPastSigma T k) (tdSamplingLaw M π T) := by
  simpa only [tdLayerSigma, tdPastSigma, IndepFun_iff_Indep] using (tdPast_indep_layer M π T k).symm

theorem tdFreshIndicator_strong_layer (T k : ℕ) (hk : k < T) (s x : State) :
    StronglyMeasurable[tdLayerSigma T k] (tdFreshIndicator T k hk s x) := by
  classical
  let f : ((i : tdLayerIndices (State := State) T k) → State) → ℝ := fun code ↦
    if code ⟨(s,(⟨k+1,by omega⟩ : Fin (T+1))), by simp [tdLayerIndices]⟩ = x then 1 else 0
  have hf : Measurable f := measurable_of_countable _
  have hc : Measurable[tdLayerSigma T k] (tdLayerData (State := State) T k) := comap_measurable _
  exact (hf.comp hc).stronglyMeasurable

/-- The distinct actual fresh policy-row indicators are independent by the
joint product law, without conditioning or an independence premise. -/
theorem tdFreshIndicators_indep (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (T k : ℕ) (hk : k < T) (s r x y : State) (hsr : s ≠ r) :
    IndepFun (tdFreshIndicator T k hk s x) (tdFreshIndicator T k hk r y) (tdSamplingLaw M π T) := by
  classical
  let i : State × Fin (T+1) := (s,⟨k+1,by omega⟩)
  let j : State × Fin (T+1) := (r,⟨k+1,by omega⟩)
  have hij : i ≠ j := by intro he; exact hsr (congrArg Prod.fst he)
  have hp := (tdSamplingLaw_independent M π T).indepFun hij
  let f : State → ℝ := fun z ↦ if z = x then 1 else 0
  let g : State → ℝ := fun z ↦ if z = y then 1 else 0
  exact hp.comp (measurable_of_countable f) (measurable_of_countable g)

/-- Conditional joint indicator mean is DERIVED from actual whole-layer/past
independence and the distinct-coordinate joint product law. -/
theorem tdFreshIndicators_condExp_mul (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (T k : ℕ) (hk : k < T) (s r x y : State) (hsr : s ≠ r) :
    (tdSamplingLaw M π T)[tdFreshIndicator T k hk s x * tdFreshIndicator T k hk r y | tdPastSigma T k]
      =ᵐ[tdSamplingLaw M π T] fun _ ↦ (M.policyTransition π s).prob x * (M.policyTransition π r).prob y := by
  have hcond := condExp_indep_eq (tdLayerSigma_le T k) (tdPastSigma_le T k)
    ((tdFreshIndicator_strong_layer T k hk s x).mul (tdFreshIndicator_strong_layer T k hk r y))
    (tdLayerSigma_indep_past M π T k)
  have hint := (tdFreshIndicators_indep M π T k hk s r x y hsr).integral_mul_eq_mul_integral
    (measurable_of_countable _).aestronglyMeasurable (measurable_of_countable _).aestronglyMeasurable
  rw [tdFreshIndicator_integral M π T k hk s x, tdFreshIndicator_integral M π T k hk r y] at hint
  filter_upwards [hcond] with data hd
  simpa only [hint] using hd

/-- Actual off-diagonal conditional covariance of synchronous TD noise is
zero given precisely the used source-time prefix. No martingale fact is assumed. -/
theorem tdRowIncrement_condExp_cross (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T k : ℕ) (hk : k < T) (V₀ : State → ℝ) (s r : State) (hsr : s ≠ r) :
    (tdSamplingLaw M π T)[tdCrossRowNoise M π η T k hk V₀ s r | tdPastSigma T k]
      =ᵐ[tdSamplingLaw M π T] fun _ ↦ 0 := by
  classical
  let c : State × State → TDSamples State T → ℝ := fun z data ↦
    (tdValueBefore M π η T k V₀ data z.1 - tdRowMean M π s (tdValueBefore M π η T k V₀ data)) *
      (tdValueBefore M π η T k V₀ data z.2 - tdRowMean M π r (tdValueBefore M π η T k V₀ data))
  let J (z : State × State) := tdFreshIndicator T k hk s z.1 * tdFreshIndicator T k hk r z.2
  have hc : ∀ z, StronglyMeasurable[tdPastSigma T k] (c z) := by
    intro z
    exact ((tdValueBefore_stronglyMeasurable M π η T k hk.le V₀ z.1).sub
      (tdRowMean_stronglyMeasurable M π η T k hk.le V₀ s)).mul
        ((tdValueBefore_stronglyMeasurable M π η T k hk.le V₀ z.2).sub
          (tdRowMean_stronglyMeasurable M π η T k hk.le V₀ r))
  have he : tdCrossRowNoise M π η T k hk V₀ s r = ∑ z, c z * J z := by
    funext data
    simpa only [Fintype.sum_prod_type, Finset.sum_apply, Pi.mul_apply, c, J] using
      tdCrossRowNoise_indicator_expansion M π η T k hk V₀ s r data
  rw [he]
  have hsum := condExp_finset_sum (μ := tdSamplingLaw M π T) (s := Finset.univ)
    (f := fun z ↦ c z * J z) (fun z hz ↦ tdSampling_integrable M π T _) (tdPastSigma T k)
  have hterms (z : State × State) :
      (tdSamplingLaw M π T)[c z * J z | tdPastSigma T k] =ᵐ[tdSamplingLaw M π T]
        fun data ↦ c z data * ((M.policyTransition π s).prob z.1 * (M.policyTransition π r).prob z.2) := by
    exact (condExp_mul_of_stronglyMeasurable_left (hc z) (tdSampling_integrable M π T _)
      (tdSampling_integrable M π T _)).trans
        ((Filter.EventuallyEq.refl _ _).mul (tdFreshIndicators_condExp_mul M π T k hk s r z.1 z.2 hsr))
  filter_upwards [hsum, ae_all_iff.mpr hterms] with data hd hterms'
  rw [hd]
  simp only [Finset.sum_apply]
  calc
    _ = ∑ z : State × State, c z data *
        ((M.policyTransition π s).prob z.1 * (M.policyTransition π r).prob z.2) :=
      Finset.sum_congr rfl (fun z hz ↦ hterms' z)
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      simpa only [c, tdRowMean] using td_centered_product_sum_eq_zero
        (M.policyTransition π s) (M.policyTransition π r) (tdValueBefore M π η T k V₀ data)

/- These raw conditional moments apply to a fixed terminal t through the
DETERMINISTIC chronological propagator. Nonnegative row coefficients, weighted
conditional variance, the genuine prefix filtration and Freedman caps remain
separate proof obligations. No terminal-independent Z sequence is substituted. -/
end StatisticalRL.TemporalDifference

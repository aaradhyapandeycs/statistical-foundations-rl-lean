import Formalization.ModelFree.QLearningConditionalPullout

/-! Conditional mean and variance of the actual Q-learning increment. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Action := ⊤

/-- The actual row mean of the predictable value is F_t-strongly measurable. -/
theorem qRowMean_stronglyMeasurable_past (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t ≤ T) (Q₀ : State → Action → ℝ) (s : State) (a : Action) :
    StronglyMeasurable[qPastSigma T t] (fun data : QSamples State Action T ↦
      qRowMean M s a (qValueBefore M η T t Q₀ data)) := by
  classical
  unfold qRowMean
  exact Finset.stronglyMeasurable_fun_sum _ fun x hx ↦
    stronglyMeasurable_const.mul (qValue_stronglyMeasurable_past M η T t ht Q₀ x)

/-- The fresh-value conditional mean equals its actual transition-row mean. -/
theorem qFresh_value_condExp (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t < T) (Q₀ : State → Action → ℝ) (s : State) (a : Action) :
    (qSamplingLaw M T)[(fun data ↦ qValueBefore M η T t Q₀ data
      (data ((s,a), ⟨t,ht⟩))) | qPastSigma T t] =ᵐ[qSamplingLaw M T]
      fun data ↦ qRowMean M s a (qValueBefore M η T t Q₀ data) := by
  classical
  have heq : (fun data : QSamples State Action T ↦ qValueBefore M η T t Q₀ data
      (data ((s,a), ⟨t,ht⟩))) =
      ∑ x, (fun data ↦ qValueBefore M η T t Q₀ data x) *
        qFreshIndicator T t ht s a x := by
    funext data
    simpa only [Finset.sum_apply, Pi.mul_apply] using
      qFresh_value_decomposition M η T t ht Q₀ s a data
  rw [heq]
  have h := qFresh_predictable_sum_condExp M T t ht s a
    (fun x data ↦ qValueBefore M η T t Q₀ data x)
    (fun x ↦ qValue_stronglyMeasurable_past M η T t (Nat.le_of_lt ht) Q₀ x)
  filter_upwards [h] with data hd
  simpa [qRowMean, Finset.sum_apply, mul_comm] using hd

/-- Actual centered Q-learning transition fluctuation has conditional mean zero. -/
theorem qRowIncrement_condExp_zero (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t < T) (Q₀ : State → Action → ℝ) (s : State) (a : Action) :
    (qSamplingLaw M T)[qRowIncrement M η T t ht Q₀ s a | qPastSigma T t]
      =ᵐ[qSamplingLaw M T] fun _ ↦ 0 := by
  let f : QSamples State Action T → ℝ := fun data ↦
    qValueBefore M η T t Q₀ data (data ((s,a), ⟨t,ht⟩))
  let g : QSamples State Action T → ℝ := fun data ↦
    qRowMean M s a (qValueBefore M η T t Q₀ data)
  have hg : (qSamplingLaw M T)[g | qPastSigma T t] = g :=
    condExp_of_stronglyMeasurable (qPastSigma_le T t)
      (qRowMean_stronglyMeasurable_past M η T t (Nat.le_of_lt ht) Q₀ s a)
      (qSampling_integrable M T g)
  have h := condExp_sub (qSampling_integrable M T f) (qSampling_integrable M T g) (qPastSigma T t)
  change (qSamplingLaw M T)[f - g | qPastSigma T t] =ᵐ[qSamplingLaw M T] _
  filter_upwards [h, qFresh_value_condExp M η T t ht Q₀ s a] with data hd hv
  change (qSamplingLaw M T)[f | qPastSigma T t] data = g data at hv
  rw [hg] at hd
  simp only [Pi.sub_apply, hv, sub_self] at hd
  exact hd

/-- The conditional square equals the actual true-row variance of V_t. -/
theorem qRowIncrement_condExp_sq (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t < T) (Q₀ : State → Action → ℝ) (s : State) (a : Action) :
    (qSamplingLaw M T)[(fun data ↦ (qRowIncrement M η T t ht Q₀ s a data)^2) | qPastSigma T t]
      =ᵐ[qSamplingLaw M T] fun data ↦ qRowVariance M s a (qValueBefore M η T t Q₀ data) := by
  classical
  let c : State → QSamples State Action T → ℝ := fun x data ↦
    (qValueBefore M η T t Q₀ data x - qRowMean M s a (qValueBefore M η T t Q₀ data))^2
  have hc : ∀ x, StronglyMeasurable[qPastSigma T t] (c x) := by
    intro x
    exact ((qValue_stronglyMeasurable_past M η T t (Nat.le_of_lt ht) Q₀ x).sub
      (qRowMean_stronglyMeasurable_past M η T t (Nat.le_of_lt ht) Q₀ s a)).pow 2
  have heq : (fun data : QSamples State Action T ↦ (qRowIncrement M η T t ht Q₀ s a data)^2) =
      ∑ x, c x * qFreshIndicator T t ht s a x := by
    funext data
    simpa only [c, Finset.sum_apply, Pi.mul_apply] using
      qFresh_increment_sq_decomposition M η T t ht Q₀ s a data
  rw [heq]
  have h := qFresh_predictable_sum_condExp M T t ht s a c hc
  filter_upwards [h] with data hd
  simpa [c, qRowVariance, Finset.sum_apply, mul_comm] using hd

end StatisticalRL.QLearning

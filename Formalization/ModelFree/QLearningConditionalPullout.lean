import Formalization.ModelFree.QLearningIndicatorCondExp
import Formalization.Probability.EmpiricalRow

/-! Actual indicator means and predictable finite-sum conditional expectations. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Action := ⊤

/-- The fresh indicator has the actual transition probability as its integral. -/
theorem qFreshIndicator_integral (M : DiscountedMDP State Action) (T t : ℕ)
    (ht : t < T) (s : State) (a : Action) (x : State) :
    ∫ data, qFreshIndicator T t ht s a x data ∂qSamplingLaw M T =
      (M.transition s a).prob x := by
  classical
  let v : State → ℝ := fun y ↦ if y = x then 1 else 0
  have hmap := qSamplingLaw_marginal M T s a ⟨t,ht⟩
  have hv : Integrable v ((qSamplingLaw M T).map
      (fun data : QSamples State Action T ↦ data ((s,a), ⟨t,ht⟩))) := Integrable.of_finite
  have h := integral_map (μ := qSamplingLaw M T) (measurable_pi_apply ((s,a), (⟨t,ht⟩ : Fin T))).aemeasurable hv.aestronglyMeasurable
  rw [hmap, FiniteDistribution.rowMeasure_integral] at h
  simpa [v, qFreshIndicator, FiniteDistribution.expectation] using h.symm

/-- Scalar fresh-state indicator conditional expectation under the full past. -/
theorem qFreshIndicator_condExp (M : DiscountedMDP State Action) (T t : ℕ)
    (ht : t < T) (s : State) (a : Action) (x : State) :
    (qSamplingLaw M T)[qFreshIndicator T t ht s a x | qPastSigma T t] =ᵐ[qSamplingLaw M T]
      fun _ ↦ (M.transition s a).prob x := by
  filter_upwards [qFreshIndicator_condExp_integral M T t ht s a x] with data hdata
  simpa [qFreshIndicator_integral M T t ht s a x] using hdata

/-- Finite predictable coefficients may be pulled past the conditional mean
of the actual fresh-state indicators. No bounded-iterate assumption is needed
on this finite experiment. -/
theorem qFresh_predictable_sum_condExp (M : DiscountedMDP State Action) (T t : ℕ)
    (ht : t < T) (s : State) (a : Action)
    (c : State → QSamples State Action T → ℝ)
    (hc : ∀ x, StronglyMeasurable[qPastSigma T t] (c x)) :
    (qSamplingLaw M T)[∑ x, c x * qFreshIndicator T t ht s a x | qPastSigma T t]
      =ᵐ[qSamplingLaw M T] ∑ x, fun data ↦ c x data * (M.transition s a).prob x := by
  classical
  have hsum := condExp_finset_sum (μ := qSamplingLaw M T) (s := Finset.univ)
    (f := fun x ↦ c x * qFreshIndicator T t ht s a x)
    (fun x hx ↦ qSampling_integrable M T _) (qPastSigma T t)
  filter_upwards [hsum, ae_all_iff.mpr (fun x ↦
    (condExp_mul_of_stronglyMeasurable_left (hc x)
      (qSampling_integrable M T _) (qSampling_integrable M T _)).trans
      ((Filter.EventuallyEq.refl _ _).mul (qFreshIndicator_condExp M T t ht s a x)))] with data hdata hterms
  rw [hdata]
  simp only [Finset.sum_apply, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  exact hterms x

/- Instantiating c with qValueBefore and separately with (V_t − PV_t)^2
requires F_t-strong measurability of each coefficient, then condExp_sub and
condExp_of_stronglyMeasurable for the predictable row mean. Those steps remain
unproved; the exact conditional variance and Freedman bridge are not asserted. -/
end StatisticalRL.QLearning

import Formalization.ModelFree.TDSamplingDefinitions
import Formalization.Generative.ModelBasedPolicyEvaluation

/-! Finite-time actual synchronous policy-TD sampling experiment. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdStateMeasurable : MeasurableSpace State := ⊤

instance tdSamplingLaw_probability (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (T : ℕ) : IsProbabilityMeasure (tdSamplingLaw M π T) := by
  unfold tdSamplingLaw
  infer_instance

/-- Every time/state coordinate has the true policy transition law. -/
theorem tdSamplingLaw_marginal (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (T : ℕ) (s : State) (t : Fin (T + 1)) :
    (tdSamplingLaw M π T).map (fun data ↦ data (s,t)) =
      (M.policyTransition π s).rowMeasure :=
  ModelBasedPolicyEvaluation.samplingLaw_marginal M π (T + 1) (s,t)

/-- All state/time draws are mutually independent under the actual law. -/
theorem tdSamplingLaw_independent (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (T : ℕ) :
    iIndepFun (fun i (data : TDSamples State T) ↦ data i) (tdSamplingLaw M π T) :=
  ModelBasedPolicyEvaluation.samplingLaw_independent M π (T + 1)

/-- The finite-array TD output is measurable. -/
theorem tdSampledIterate_measurable (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) :
    Measurable (tdSampledIterate M π η T V₀) := measurable_of_countable _

/-- The deterministic bounded-iterate theorem holds for every outcome of the
actual sampling law, hence almost surely. -/
theorem tdSampledIterate_bounds_ae (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (hη : ∀ k, k ≤ T → 0 ≤ η k ∧ η k ≤ 1) :
    ∀ᵐ data ∂tdSamplingLaw M π T, ∀ s,
      0 ≤ tdSampledIterate M π η T V₀ data s ∧
        tdSampledIterate M π η T V₀ data s ≤ M.effectiveHorizon := by
  exact Filter.Eventually.of_forall (fun data s ↦
    tdIterate_bounds M π η (tdSamplesExtend M T data) V₀ h₀ T hη s)

end StatisticalRL.TemporalDifference

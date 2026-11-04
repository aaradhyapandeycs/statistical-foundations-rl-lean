import Formalization.ModelFree.TDIterateBounds
import Formalization.Statements.Ch3Definitions

/-! Definitions for the actual finite synchronous TD sampling experiment.
The matching probability facts are proved in `TDSynchronousSampling`. -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSamplingDefinitionsStateMeasurable : MeasurableSpace State := ⊤

/-- Independent draws from the evaluated policy row, indexed by state and
algorithm time 0,...,T. Time 0 is unused by the TD update. -/
abbrev TDSamples (State : Type*) (T : ℕ) :=
  StatisticalRL.ModelBasedPolicyEvaluation.Samples State (T + 1)

/-- The actual finite product law of all synchronous row draws. -/
noncomputable def tdSamplingLaw (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (T : ℕ) : Measure (TDSamples State T) :=
  StatisticalRL.ModelBasedPolicyEvaluation.samplingLaw M π (T + 1)

/-- Extend the observed finite array outside its horizon by a fixed state.
Only coordinates 1,...,T affect the iterate at T. -/
noncomputable def tdSamplesExtend (M : DiscountedMDP State Action) (T : ℕ)
    (data : TDSamples State T) : ℕ → State → State := fun t s ↦
  if h : t < T + 1 then data (s, ⟨t,h⟩) else Classical.choice M.state_nonempty

/-- The actual TD output at time T from the finite sampled array. -/
noncomputable def tdSampledIterate (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (data : TDSamples State T) : State → ℝ :=
  tdIterate M π η (tdSamplesExtend M T data) V₀ T

end StatisticalRL.TemporalDifference

import Formalization.ModelFree.TDSamplingDefinitions

/-! The exact-T synchronous policy-TD source experiment. -/
open MeasureTheory
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSourceSamplingStateMeasurable : MeasurableSpace State := ⊤

/-- One true policy-row draw per state and update, indexed from zero. -/
abbrev TDSourceSamples (State : Type*) (T : ℕ) :=
  StatisticalRL.ModelBasedPolicyEvaluation.Samples State T

/-- The product law of exactly T independent policy-row draws per state. -/
noncomputable def tdSourceSamplingLaw (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (T : ℕ) : Measure (TDSourceSamples State T) :=
  StatisticalRL.ModelBasedPolicyEvaluation.samplingLaw M π T

/-- Update k reads draw k-1 when 1 ≤ k ≤ T; other coordinates are unused. -/
noncomputable def tdSourceSamplesExtend (M : DiscountedMDP State Action) (T : ℕ)
    (data : TDSourceSamples State T) : ℕ → State → State := fun k s ↦
  if h : 1 ≤ k ∧ k ≤ T then data (s, ⟨k - 1, by omega⟩)
  else Classical.choice M.state_nonempty

/-- Source TD output after T updates under the exact-T experiment. -/
noncomputable def tdSourceSampledIterate (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (data : TDSourceSamples State T) : State → ℝ :=
  tdIterate M π η (tdSourceSamplesExtend M T data) V₀ T

/-- Discard the unused time-zero layer of the padded experiment. -/
def tdUsedSampleProjection (T : ℕ) (data : TDSamples State T) : TDSourceSamples State T :=
  fun i ↦ data (i.1, i.2.succ)

end StatisticalRL.TemporalDifference

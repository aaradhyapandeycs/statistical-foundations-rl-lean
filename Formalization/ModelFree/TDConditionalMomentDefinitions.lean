import Formalization.ModelFree.TDCausality
import Formalization.ModelFree.TDActualErrorDecomposition

namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdMomentDefinitionsStateMeasurable : MeasurableSpace State := ⊤

noncomputable def tdValueBefore (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (data : TDSamples State T) : State → ℝ :=
  tdIterate M π η (tdSamplesExtend M T data) V₀ t

end StatisticalRL.TemporalDifference

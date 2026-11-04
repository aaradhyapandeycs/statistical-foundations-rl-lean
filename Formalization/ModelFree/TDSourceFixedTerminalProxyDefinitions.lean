import Formalization.ModelFree.TDSharpEnergyProxy
import Formalization.ModelFree.TDSourceRateProxyTransport
import Formalization.ModelFree.TDSourceFreedmanBudgetSmallness

namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdProxyDefinitionsStateMeasurable : MeasurableSpace State := ⊤

/-- Vector of actual squared-TD proxy coordinates at one terminal. -/
noncomputable def tdSourceFixedTerminalProxyVector
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (V₀ : State → ℝ) (barη : ℝ)
    (data : TDSamples State T) : State → ℝ :=
  fun q ↦ tdSquareLateWindowRandomProxy M π η T t V₀ barη q data

end StatisticalRL.TemporalDifference

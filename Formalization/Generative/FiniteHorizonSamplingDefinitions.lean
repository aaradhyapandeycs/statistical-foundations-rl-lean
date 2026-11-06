import Formalization.MDP.EnvironmentDefinitions
import Formalization.Probability.FiniteSampleDefinitions
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance ch3FiniteStageStateMeasurable : MeasurableSpace State := ⊤
abbrev SampleIndex (State Action : Type*) (H N : ℕ) := (Fin H × State × Action) × Fin N

abbrev Samples (State Action : Type*) (H N : ℕ) := SampleIndex State Action H N → State

/-- N actual independent next-state observations at every stage/state/action. -/
noncomputable def samplingLaw {H : ℕ} (E : Fin H → EnvironmentStage State Action) (N : ℕ) :
    Measure (Samples State Action H N) :=
  Measure.pi (fun i : SampleIndex State Action H N ↦
    ((E i.1.1).transition i.1.2.1 i.1.2.2).rowMeasure)


end StatisticalRL.FiniteHorizonGenerative

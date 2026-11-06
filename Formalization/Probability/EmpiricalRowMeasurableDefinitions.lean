import Formalization.Probability.FiniteSampleDefinitions
open MeasureTheory
namespace StatisticalRL.FiniteDistribution
variable {State : Type*} [Fintype State]
local instance empiricalRowStateMeasurable : MeasurableSpace State := ⊤
end StatisticalRL.FiniteDistribution

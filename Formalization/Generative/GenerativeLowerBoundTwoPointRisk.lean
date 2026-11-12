import Formalization.Generative.GenerativeLowerBoundFamilyFano
import Formalization.Generative.GenerativeLowerBoundFamilyDecision
import Formalization.Generative.GenerativeLowerBoundKLAffinity

/-! Actual two-point family testing to trajectory-Q policy risk. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance twoPointRiskStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance twoPointRiskFinMeasurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤

end StatisticalRL.GenerativeLowerBound

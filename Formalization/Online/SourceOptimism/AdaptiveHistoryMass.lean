import Formalization.Online.SourceOptimism.StackRunCylinderIdentity
import Formalization.Online.SourceOptimism.DistinctCylinderMass
import Formalization.Online.SourceOptimism.VisitCoordinateDistinct

/-! actual adaptive stack run-history masses.
The separate source online trajectory selector/path law is not assumed equal. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Row Outcome : Type*} [Fintype Row] [DecidableEq Row] [Fintype Outcome]
local instance onlineAdaptiveHistoryOutcomeMeasurable : MeasurableSpace Outcome := ⊤

/-- Total extension of a finite successor array. The arbitrary fallback is
never read by the bounded transcript event below. -/
def onlineFiniteStackExtend (K : ℕ) (fallback : Outcome)
    (data : Row × Fin K → Outcome) (r : Row) (n : ℕ) : Outcome :=
  if hn : n<K then data (r,⟨n,hn⟩) else fallback

end StatisticalRL.OnlineRL

import Formalization.Online.Regret.MVP.Optimism.MVPTrueSuffixBonus
import Formalization.Online.SourceOptimism.EpisodicStackSelector

/-! Source-only candidate equating the two presentations of the same finite
product of transition rows. The reset-vector product is handled separately. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance mvpExpandedStackStateMeasurable : MeasurableSpace State := ⊤

theorem mvp_expandedSamplingLaw_eq_stackLaw {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (K : ℕ) :
    StatisticalRL.FiniteHorizonGenerative.samplingLaw E K =
      onlineMDPStackLaw E K := by
  rfl

end StatisticalRL.OnlineRL

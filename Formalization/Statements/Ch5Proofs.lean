import Formalization.Statements.Ch5
import Formalization.Online.SourceOptimism.SourceOptimismAllocation

namespace StatisticalRL.Statements
open StatisticalRL.OnlineRL

theorem Lemma5_5_corrected_holds : Lemma5_5_corrected := by
  intro State Action instS instA H K hH hK E ρ δ c₁ c₂ hδ hδone hc₁ hc₂
  simpa only [onlineSourceOptimismDeltaPrime, onlineHistoryAllStageTrajectoryOptimism] using
    onlineSourceAllocated_allStageTrajectoryOptimism_strict H K hH hK E ρ (Classical.choice (E ⟨0, hH⟩).state_nonempty) δ c₁ c₂
      hδ hδone hc₁ hc₂
end StatisticalRL.Statements

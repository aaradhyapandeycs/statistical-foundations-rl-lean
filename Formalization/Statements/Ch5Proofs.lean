import Formalization.Statements.Ch5
import Formalization.Online.SourceOptimism.SourceOptimismAllocation
import Formalization.Online.Regret.NonnegativeTelescope

namespace StatisticalRL.Statements
open StatisticalRL.OnlineRL

theorem Lemma5_5_corrected_holds : Lemma5_5_corrected := by
  intro State Action instS instA H K hH hK E ρ δ c₁ c₂ hδ hδone hc₁ hc₂
  simpa only [onlineSourceOptimismDeltaPrime, onlineHistoryAllStageTrajectoryOptimism] using
    onlineSourceAllocated_allStageTrajectoryOptimism_strict H K hH hK E ρ (Classical.choice (E ⟨0, hH⟩).state_nonempty) δ c₁ c₂
      hδ hδone hc₁ hc₂

/-- Consume the nonnegative-parameter telescope for the printed log scale. -/
theorem Lemma5_6_corrected_holds : Lemma5_6_corrected := by
  intro State Action instS instA instNS instNA H hH stage state action δ' c₁ c₂
    hδ' hδone hc₁ hc₂ hgreedy
  have hratio : (1 : ℝ) ≤ 1 / δ' :=
    (le_div_iff₀ hδ').2 (by simpa using hδone)
  have hL : 0 ≤ Real.log (1 / δ') := Real.log_nonneg hratio
  have h := onlineCappedEpisode_realized_telescope_nonnegative H stage state action
    (Real.log (1 / δ')) c₁ c₂ hL hc₁ hc₂ (fun _ => inferInstance) hgreedy
  simpa only [onlineCappedEpisodeValueAlongPath, List.drop_zero,
    onlineCappedEpisodeTelescopeSummand] using h

end StatisticalRL.Statements

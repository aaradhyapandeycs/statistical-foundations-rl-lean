import Formalization.Online.Regret.T4.OnlineRegretT4EpisodeAzuma

/-! equality between the actual block process and the public
source T4 regret-decomposition array. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]

theorem onlineActualEpisodeT4_eq_episodeIncrement
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath.{uState, 0} State (K * H)) (k : Fin K)
    (δ c₁ c₂ : ℝ) :
    (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ c₁ c₂).2.2.2 =
      onlineT4EpisodeIncrement H K hH E initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) path k := by
  unfold onlineActualEpisodeRegretTerms onlineT4EpisodeIncrement onlineT4EpisodeReturn
  simp only [onlineT4SelectedEpisodeValue_eq_capped]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnH := Finset.mem_range.mp hn
  simp only [onlineCappedEpisodeReward, dif_pos hnH, onlineT4EpisodeState,
    onlineT4PlayedAction]

theorem onlineT4PaddedEpisodeSum_eq_publicT4
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    (∑ n ∈ Finset.range K,
      onlineT4PaddedEpisodeY H K hH E fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) n sample) =
    ∑ k : Fin K,
      (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ c₁ c₂).2.2.2 := by
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [onlineT4PaddedEpisodeY, dif_pos k.isLt]
  exact (onlineActualEpisodeT4_eq_episodeIncrement H K hH E sample.1 fallback sample.2 k δ c₁ c₂).symm

end StatisticalRL.OnlineRL

import Formalization.Online.Regret.Definitions
import Formalization.Online.Regret.Telescope

/-! Actual-path UCBVI SummedEpisodes; no regret-rate theorem is claimed. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Summing the actual-history episode inequalities on the same realized
path gives the four source-shaped totals. The optimism premise is exactly the
pathwise event consumed by the episode theorem. -/
theorem onlineActualRegret_le_four_terms
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H))
    (δ' c₁ c₂ : ℝ) (hδ' : 0 < δ') (hδ'small : δ' ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁ ^ 2 ≤ c₂)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ' c₁ c₂
      (onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂))
        (K * H) [] path)) :
    (∑ k : Fin K, onlineActualEpisodeRegret H K hH E initial fallback path k δ' c₁ c₂) ≤
      (∑ k : Fin K, (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).1) +
      (∑ k : Fin K, (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).2.1) +
      (∑ k : Fin K, (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).2.2.1) +
      (∑ k : Fin K, (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).2.2.2) := by
  classical
  have hepisode : ∀ k : Fin K,
      onlineActualEpisodeRegret H K hH E initial fallback path k δ' c₁ c₂ ≤
      (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).1 +
      (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).2.1 +
      (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).2.2.1 +
      (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).2.2.2 := by
    intro k
    simpa [onlineActualEpisodeRegret, onlineActualEpisodeRegretTerms] using
      onlineSequentialEpisode_regret_decomposition H K hH E initial fallback path k δ' c₁ c₂
        hδ' hδ'small hc₁ hc₂ hoptimism
  calc
    _ ≤ ∑ k : Fin K,
        ((onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).1 +
         (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).2.1 +
         (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).2.2.1 +
         (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).2.2.2) :=
      Finset.sum_le_sum (fun k _ ↦ hepisode k)
    _ = _ := by simp only [Finset.sum_add_distrib]

end StatisticalRL.OnlineRL

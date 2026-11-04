import Formalization.Online.Regret.Definitions
import Formalization.Online.Regret.SummedEpisodes

/-! Actual-path UCBVI FixedOptimalSplit; no regret-rate theorem is claimed. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]

private theorem onlineEpisodeT1_eq_W1_add_W2
    (H : ℕ) (E : Fin H → EnvironmentStage State Action)
    (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action) (L c₁ c₂ : ℝ) (n : ℕ) :
    onlineCappedEpisodeT1 H stage state action L c₁ c₂ n =
      onlineEpisodeFixedOptimalW1 H E stage state action n +
      onlineEpisodeFixedOptimalW2 H E stage state action L c₁ c₂ n := by
  unfold onlineCappedEpisodeT1 onlineEpisodeFixedOptimalW1 onlineEpisodeFixedOptimalW2
  split_ifs with hn
  · simp only [FiniteDistribution.expectation_sub]
    ring
  · ring

/-- Source T₁ split on the same actual trajectory and completed-history
planner, with the true optimal continuation of the same environment. -/
theorem onlineActualT1_eq_W1_add_W2
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (δ' c₁ c₂ : ℝ) :
    (∑ k : Fin K, (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ' c₁ c₂).1) =
      (∑ k : Fin K, onlineActualEpisodeW1 H K hH E initial fallback path k δ' c₁ c₂) +
      (∑ k : Fin K, onlineActualEpisodeW2 H K hH E initial fallback path k δ' c₁ c₂) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [onlineActualEpisodeRegretTerms, onlineActualEpisodeW1, onlineActualEpisodeW2]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact onlineEpisodeT1_eq_W1_add_W2 H E _ _ _ _ c₁ c₂ n

end StatisticalRL.OnlineRL

import Formalization.Online.Regret.T0.OnlineT0ActualSuffix
import Formalization.Online.Regret.Joint.OnlineW123Singleton

/-! Same-experiment suffix proof component: OnlineT0Singleton.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineSingleton_expectation_eq_value [Subsingleton State]
    (p : FiniteDistribution State) (V : State → ℝ) (x : State) : p.expectation V = V x := by
  calc
    _ = (EnvironmentStage.pointMass x).expectation V := onlineSingleton_expectation_eq p _ V
    _ = _ := EnvironmentStage.expectation_pointMass x V

theorem onlineSingleton_suffix_T1_zero [Subsingleton State]
    (H : ℕ) (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action) (L c₁ c₂ : ℝ) (n : ℕ) :
    onlineCappedEpisodeT1 H stage state action L c₁ c₂ n = 0 := by
  unfold onlineCappedEpisodeT1
  split_ifs with hn
  · exact sub_eq_zero.mpr (onlineSingleton_expectation_eq _ _ _)
  · rfl

theorem onlineSingleton_suffix_T3_zero [Subsingleton State]
    (H : ℕ) (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action) (L c₁ c₂ : ℝ) (n : ℕ) :
    onlineCappedEpisodeT3 H stage state action L c₁ c₂ n = 0 := by
  unfold onlineCappedEpisodeT3
  split_ifs with hn
  · dsimp only
    rw [onlineSingleton_expectation_eq_value _ _ (state (n + 1))]
    exact sub_self _
  · rfl

theorem onlineSingleton_suffix_T4_zero [Subsingleton State]
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (j : ℕ) (k : Fin K)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    onlineT4SuffixEpisodeIncrement H K hH E fallback planner j k sample = 0 := by
  unfold onlineT4SuffixEpisodeIncrement
  apply Finset.sum_eq_zero
  intro h hh
  rw [onlineT4ActualStep_eq_policy_noise H K hH E fallback planner k h sample]
  rw [onlineSingleton_expectation_eq_value _ _
    (onlineT4EpisodeState H K sample.1 fallback
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2)
      k.val (h.val + 1))]
  exact sub_self _
end StatisticalRL.OnlineRL

import Formalization.Online.Regret.T0.OnlineT0ActualCharge
import Formalization.Online.Regret.W12.OnlineW12SuffixIota

/-! Same-experiment suffix proof component: OnlineT0ActualW12Points.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineT0ActualSuffix_T1_eq_W1_add_W2
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) (n : ℕ) :
    let stage := onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k
    let state := onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k
    let action := onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k
    onlineCappedEpisodeT1 H stage state action (Real.log (1 / δ)) c₁ c₂ n =
      onlineEpisodeFixedOptimalW1 H E stage state action n +
      onlineEpisodeFixedOptimalW2 H E stage state action (Real.log (1 / δ)) c₁ c₂ n := by
  unfold onlineCappedEpisodeT1 onlineEpisodeFixedOptimalW1 onlineEpisodeFixedOptimalW2
  split_ifs with hn
  · simp only [FiniteDistribution.expectation_sub]
    ring
  · ring

theorem onlineT0ActualSuffix_W12_points
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) (h : Fin H) :
    let stage := onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k
    let state := onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k
    let action := onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k
    onlineEpisodeFixedOptimalW1 H E stage state action h.val =
      onlineActualW1Point H K hH E initial fallback path δ c₁ c₂ h k ∧
    onlineEpisodeFixedOptimalW2 H E stage state action (Real.log (1 / δ)) c₁ c₂ h.val =
      onlineActualW2Point H K hH E initial fallback path δ c₁ c₂ h k := by
  classical
  have halign := onlineActualStageRow_eq_episodeStateAction H K hH E initial fallback path k h δ c₁ c₂
  have hopt : DecisionStage.trajectoryValue ((EnvironmentStage.greedyStages (List.ofFn E)).drop (h.val + 1)) =
      EnvironmentStage.optimalValue ((List.ofFn E).drop (h.val + 1)) := by
    funext x
    exact EnvironmentStage.greedy_suffix_value (List.ofFn E) (h.val + 1) x
  have hs : onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k =
      (fun i => onlineHistoryPlanningStage E ((onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂))
        (K * H) [] path).take (k.val * H)) i) := by
    funext i
    rfl
  rw [hs]
  constructor
  · simp only [onlineEpisodeFixedOptimalW1, dif_pos h.isLt]
    dsimp [onlineActualW1Point]
    rw [halign]
    simp [hopt, onlineT0ActualSuffixStage, onlineT0ActualSuffixState, onlineT0ActualSuffixAction,
      onlineT4EpisodeState, onlineT4PlayedAction, onlineTrueSuffixRowFamily,
      onlineFixedOptimalContinuation, EnvironmentStage.greedy_suffix_value, onlineHistoryPlanningStage, h.isLt]
  · simp only [onlineEpisodeFixedOptimalW2, dif_pos h.isLt]
    dsimp [onlineActualW2Point, onlineActualW2Gap, onlineActualOptimisticContinuation, onlineCappedBackwardValueAt]
    rw [halign]
    simp [hopt, onlineT0ActualSuffixStage, onlineT0ActualSuffixState, onlineT0ActualSuffixAction,
      onlineT4EpisodeState, onlineT4PlayedAction, onlinePreEpisodePlanningStages,
      onlineTrueSuffixRowFamily, onlineFixedOptimalContinuation, EnvironmentStage.greedy_suffix_value,
      onlineHistoryPlanningStage, h.isLt]
end StatisticalRL.OnlineRL


import Formalization.Online.Regret.T0.OnlineT0ActualW12Alignment
import Formalization.Online.Regret.Gap.StagePolicyGapDefinitions

/-! Same-experiment suffix proof component: OnlineT0ActualGapIdentity.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineActualStagePolicyGap_eq_suffix_gap
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (j : Fin H) (k : Fin K) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let state := onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k
    onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ j k =
      onlineCappedBackwardValueAt H (Real.log (1 / δ)) c₁ c₂
        (onlinePreEpisodePlanningStages E history k.val) j.val (state j.val) -
      DecisionStage.trajectoryValue ((EnvironmentStage.controlled (List.ofFn E)
        (onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂)).drop j.val) (state j.val) := by
  classical
  have hrow := onlineActualStageRow_eq_episodeStateAction H K hH E initial fallback path k j δ c₁ c₂
  dsimp [onlineActualStagePolicyGap]
  rw [hrow]
  rfl
end StatisticalRL.OnlineRL

import Formalization.Online.Regret.Gap.StagePolicyGapDefinitions
import Formalization.Online.Regret.Gap.OnlineT6DifferenceAssembly
import Formalization.Online.Regret.T5.OnlineT5Successor
import Formalization.Online.Regret.PolicyVariance.OnlineFrozenEpisodeVariance

/-! Actual-law variance and gap proof component: OnlineJ2ActualStage.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance j2StateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance j2ActionDecidable : DecidableEq Action := Classical.decEq Action

/-- A nonterminal stored successor is the next selected stage's actual state;
both terms use the same pre-episode optimistic table and policy. -/
theorem onlineJ2_successor_gap_eq_next_stage
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) (hn : h.val + 1 < H) :
    let x := onlineT5ActualSuccessor H K hH E initial fallback path δ c₁ c₂ h k
    onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k x -
      onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k x =
      onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ ⟨h.val + 1, hn⟩ k := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let next : Fin H := ⟨h.val + 1, hn⟩
  have hsucc := onlineT5ActualSuccessor_eq_next_state H K hH E initial fallback path δ c₁ c₂ h k hn
  have hrow := onlineActualStageRow_eq_episodeStateAction H K hH E initial fallback path k next δ c₁ c₂
  have hrowstate := congrArg Prod.fst hrow
  simp only [onlineT4EpisodeState, onlineT4PlayedAction] at hrowstate
  dsimp only
  rw [hsucc]
  unfold onlineActualStagePolicyGap
  dsimp only
  rw [hrowstate]
  rfl

/-- At the final stage both the capped optimistic and the true-policy
continuations are zero, independently of the stored terminal successor. -/
theorem onlineJ2_terminal_gap_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) (hlast : h.val + 1 = H) (s : State) :
    onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k s -
      onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k s = 0 := by
  rw [onlineActualOptimisticContinuation_terminal H K hH E initial fallback path δ c₁ c₂ h k hlast]
  unfold onlineActualPolicyContinuation
  rw [hlast, List.drop_eq_nil_of_le]
  · simp [DecisionStage.trajectoryValue_nil]
  · rw [onlineControlledStages_length, List.length_ofFn]
end StatisticalRL.OnlineRL

namespace StatisticalRL.OnlineRL
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

/-- At each actual selected state, the deployed policy is dominated by the
true optimum, which is dominated by the optimistic table on the event. -/
theorem onlineActualStagePolicyGap_nonneg
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path))
    (h : Fin H) (k : Fin K) :
    0 ≤ onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ h k := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let π := onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂
  let a : Action := Classical.choice ((E h).action_nonempty)
  have hp := (EnvironmentStage.greedy_suffix_dominates (List.ofFn E) π h.val sa.1 a).1
  have ho := (hoptimism k h).1 sa.1
  change 0 ≤ onlineCappedBackwardValueAt H (Real.log (1 / δ)) c₁ c₂
      (onlinePreEpisodePlanningStages E history k.val) h.val sa.1 -
      DecisionStage.trajectoryValue ((EnvironmentStage.controlled (List.ofFn E) π).drop h.val) sa.1
  have hp' : DecisionStage.trajectoryValue ((EnvironmentStage.controlled (List.ofFn E) π).drop h.val) sa.1 ≤
      EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) sa.1 := by
    simpa [EnvironmentStage.greedy_suffix_value] using hp
  have ho' : EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) sa.1 ≤
      onlineCappedBackwardValueAt H (Real.log (1 / δ)) c₁ c₂
        (onlinePreEpisodePlanningStages E history k.val) h.val sa.1 := by
    simpa [history, planner, EnvironmentStage.greedy_suffix_value] using ho
  linarith
end StatisticalRL.OnlineRL

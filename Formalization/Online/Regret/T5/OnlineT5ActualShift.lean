import Formalization.Online.Regret.T5.OnlineT5Successor
import Formalization.Online.Regret.T5.OnlineT5EpisodeBudget
import Formalization.Online.Regret.T2.OnlineT2ActualAlignment

/-! Actual-law variance and gap proof component: OnlineT5ActualShift.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t5ShiftStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t5ShiftActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineT5ActualSuccessor_value_eq_episode_next
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let stage := fun t : Fin H => onlineHistoryPlanningStage E (history.take (k.val * H)) t
    onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
      (onlineT5ActualSuccessor H K hH E initial fallback path δ c₁ c₂ h k) =
      onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ)) c₁ c₂
        ((List.ofFn stage).drop (h.val + 1))
        (onlineEpisodicCurrentState H K initial fallback (history.take (k.val * H + (h.val + 1)))) := by
  classical
  dsimp only
  by_cases hnext : h.val + 1 < H
  · rw [onlineT5ActualSuccessor_eq_next_state H K hH E initial fallback path δ c₁ c₂ h k hnext]
    rfl
  · have hlast : h.val + 1 = H := by omega
    rw [onlineActualOptimisticContinuation_terminal H K hH E initial fallback path δ c₁ c₂ h k hlast]
    simp only [hlast]
    rw [List.drop_eq_nil_of_le (by simp)]
    rfl
end StatisticalRL.OnlineRL

namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State : Type*} {Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance t5ActStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t5ActActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineT5_actual_episode_remainder_bound
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hL : 0 ≤ Real.log (1 / δ)) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (k : Fin K) :
    (∑ h : Fin H,
      let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
      let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
      let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
      (U (onlineT5ActualSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2 -
        ((onlineObservedPlanningRow stage sa.1 sa.2).expectation U)^2) ≤
      2 * (H : ℝ) * ((∑ h : Fin H, onlineActualT2Point H K hH E initial fallback path δ c₁ c₂ h k) + H) := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let stage := fun h : Fin H => onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let state := fun n : ℕ => onlineEpisodicCurrentState H K initial fallback (history.take (k.val * H + n))
  let action := fun n : ℕ => if hn : n < H then onlineT4PlayedAction H K hH initial fallback planner path k ⟨n, hn⟩
    else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
  have hgreedy : ∀ h : Fin H, letI : Nonempty Action := (stage h).environment.action_nonempty
      onlineCappedStageQ (H : ℝ) (Real.log (1 / δ)) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ)) c₁ c₂ ((List.ofFn stage).drop (h.val + 1)))
        (state h.val) (action h.val) =
      actionMaximum (onlineCappedStageQ (H : ℝ) (Real.log (1 / δ)) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ)) c₁ c₂ ((List.ofFn stage).drop (h.val + 1))) (state h.val)) := by
    intro h
    letI : Nonempty Action := (stage h).environment.action_nonempty
    have hmax := onlineSequentialEpisode_backup_is_greedy H K hH E initial fallback path k h
      (Real.log (1 / δ)) c₁ c₂ (E h).action_nonempty
    have hpre : (history.take (k.val * H)).take (k.val * H) = history.take (k.val * H) := by simp
    simp only [onlinePreEpisodePlanningStages, hpre] at hmax
    simpa [planner, history, stage, state, action, onlineT4PlayedAction, h.isLt, List.take_take, Nat.min_self] using hmax
  have hb := onlineT5_episode_square_budget H stage state action (Real.log (1 / δ)) c₁ c₂ hL hc₁ hc₂ hgreedy
  rw [Finset.sum_range] at hb
  have hcost : (∑ h : Fin H,
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
      (U (onlineT5ActualSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2 -
        ((onlineObservedPlanningRow (stage h) sa.1 sa.2).expectation U)^2) =
      ∑ h : Fin H,
       ((onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ)) c₁ c₂ ((List.ofFn stage).drop (h.val + 1)) (state (h.val + 1)))^2 -
       (if hn : h.val < H then (onlineObservedPlanningRow (stage ⟨h.val, hn⟩) (state h.val) (action h.val)).expectation
         (onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ)) c₁ c₂ ((List.ofFn stage).drop (h.val + 1))) else 0)^2) := by
    apply Finset.sum_congr rfl
    intro h hh
    have hr := onlineActualStageRow_eq_episodeStateAction H K hH E initial fallback path k h δ c₁ c₂
    have hs := onlineT5ActualSuccessor_value_eq_episode_next H K hH E initial fallback path δ c₁ c₂ h k
    simp only [onlineT4EpisodeState, onlineT4PlayedAction, h.isLt, dif_pos, planner, history, state, action] at hr
    simp only [dif_pos h.isLt]
    dsimp only [onlineActualOptimisticContinuation, onlineCappedBackwardValueAt] at hs ⊢
    rw [hr]
    simp only [planner, history, stage, state, action, h.isLt, dif_pos] at hs ⊢
    rw [hs]
    simp [onlinePreEpisodePlanningStages, stage, state, action, onlineT4PlayedAction, h.isLt, planner, history]
  have hcharge : (∑ h : Fin H, onlineActualT2Point H K hH E initial fallback path δ c₁ c₂ h k) =
      ∑ h : Fin H, onlineCappedEpisodeT2 H stage state action (Real.log (1 / δ)) c₁ c₂ h.val := by
    apply Finset.sum_congr rfl
    intro h hh
    have hr := onlineActualStageRow_eq_episodeStateAction H K hH E initial fallback path k h δ c₁ c₂
    simp only [onlineT4EpisodeState, onlineT4PlayedAction, h.isLt, dif_pos, planner, history, state, action] at hr
    unfold onlineActualT2Point onlineActualOptimisticContinuation onlineCappedBackwardValueAt onlineCappedEpisodeT2
    simp only [h.isLt, dif_pos]
    rw [hr]
    simp [onlinePreEpisodePlanningStages, stage, state, action, onlineT4PlayedAction, h.isLt, planner, history]
  change (∑ h : Fin H, let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
      (U (onlineT5ActualSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2 -
        ((onlineObservedPlanningRow (stage h) sa.1 sa.2).expectation U)^2) ≤ _
  rw [hcost, hcharge]
  simpa only [Finset.sum_range] using hb
end StatisticalRL.OnlineRL

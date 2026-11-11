import Formalization.Online.Regret.MVP.T6.MVPActualSuccessorValue
import Formalization.Online.Regret.MVP.T6.MVPActualGreedyAlignment
import Formalization.Online.Regret.MVP.T6.MVPActualRowAlignment
import Formalization.Online.Regret.MVP.T6.MVPVarianceEpisodeBudget
import Formalization.Online.Regret.T4.OnlineRegretT4ActualBridge

/-! Actual same-path MVP episode remainder; no optimism premise. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance t6MVPActualEpisodeRemainder_mvpRemainderStateEq : DecidableEq State := Classical.decEq State
noncomputable local instance t6MVPActualEpisodeRemainder_mvpRemainderActionEq : DecidableEq Action := Classical.decEq Action

theorem mvp_actual_episode_remainder_bound
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) (hL : 0 ≤ Real.log (1/δ)) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (k : Fin K) :
    (∑ h : Fin H,
      let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
      (U (mvpVarianceSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2 -
        (((E h).transition sa.1 sa.2).expectation U)^2) ≤
    2*(H : ℝ)*((∑ h : Fin H,
      let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
      let history := mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂
      let prehist := history.take (k.val*H)
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      letI : Nonempty State := (E h).state_nonempty
      let stage := onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback prehist)
        (onlineMVPHistoryNextAt fallback prehist) prehist.length h
      let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
      onlineRegretAnalysisCharge (H : ℝ) (Real.log (1/δ)) c₁ c₂ stage U sa.1 sa.2) + H +
      ∑ h : Fin H,
      let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
      let history := mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂
      let prehist := history.take (k.val*H)
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      letI : Nonempty State := (E h).state_nonempty
      let stage := onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback prehist)
        (onlineMVPHistoryNextAt fallback prehist) prehist.length h
      let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
      max ((onlineObservedPlanningRow stage sa.1 sa.2).expectation U -
        ((E h).transition sa.1 sa.2).expectation U) 0) := by
  classical
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
  let history := mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂
  let prehist := history.take (k.val*H)
  let stage : Fin H → OnlineObservedPlanningStage State Action := fun h =>
    letI : Nonempty State := (E h).state_nonempty
    onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback prehist)
      (onlineMVPHistoryNextAt fallback prehist) prehist.length h
  let state := fun n => onlineEpisodicCurrentState H K initial fallback (history.take (k.val*H+n))
  let action := fun n => if hn : n < H then onlineT4PlayedAction H K hH initial fallback planner path k ⟨n,hn⟩
    else Classical.choice ((E ⟨0,hH⟩).action_nonempty)
  have hrow (h : Fin H) : onlineActualStageRowSequence H K hH initial fallback planner path h k.val =
      (state h.val, action h.val) := by
    have hr := mvpActualStageRow_eq_episodeStateAction H K hH E initial fallback path k h δ c₁ c₂
    simpa [planner, history, mvpVarianceHistory, state, action, onlineT4PlayedAction, h.isLt] using hr
  have htail (h : Fin H) : mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k =
      onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂ ((List.ofFn stage).drop (h.val+1)) := by
    simp [mvpVarianceContinuation, onlineCappedBackwardValueAt, onlineMVPHistoryPlanningStages,
      planner, history, prehist, stage, mvpVarianceHistory]
  have hsucc (h : Fin H) : mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
      (mvpVarianceSuccessor H K hH E initial fallback path δ c₁ c₂ h k) =
      onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂
        ((List.ofFn stage).drop (h.val+1)) (state (h.val+1)) := by
    have hs := mvpActualSuccessor_value_eq_episode_next H K hH E initial fallback path δ c₁ c₂ h k
    simpa [planner, history, prehist, stage, state, mvpVarianceHistory,
      onlineMVPHistoryPlanningStages] using hs
  have hgreedy : ∀ h : Fin H, letI : Nonempty Action := (stage h).environment.action_nonempty
      onlineCappedStageQ (H : ℝ) (Real.log (1/δ)) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂ ((List.ofFn stage).drop (h.val+1)))
        (state h.val) (action h.val) =
      actionMaximum (onlineCappedStageQ (H : ℝ) (Real.log (1/δ)) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂ ((List.ofFn stage).drop (h.val+1))) (state h.val)) := by
    intro h
    letI : Nonempty Action := (E h).action_nonempty
    have hg := mvp_actualRow_stageGreedy H K hH E initial fallback path (Real.log (1/δ)) c₁ c₂ k h
    dsimp only at hg
    rw [hrow h] at hg
    simpa [planner, history, prehist, stage, mvpVarianceHistory,
      onlineMVPHistoryPlanningStages] using hg
  have hb := mvp_episode_trueVariance_square_budget H stage state action (Real.log (1/δ)) c₁ c₂ hL hc₁ hc₂ hgreedy
  simp only [Finset.sum_range, dif_pos, Fin.isLt] at hb
  have hcost : (∑ h : Fin H,
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
      (U (mvpVarianceSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2 -
        (((E h).transition sa.1 sa.2).expectation U)^2) =
      ∑ h : Fin H, ((onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂
        ((List.ofFn stage).drop (h.val+1)) (state (h.val+1)))^2 -
        ((stage h).environment.transition (state h.val) (action h.val)).expectation
          (onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂
            ((List.ofFn stage).drop (h.val+1))) ^ 2) := by
    apply Finset.sum_congr rfl
    intro h _
    simp only [hrow, hsucc, htail]
    rfl
  have hcharge : (∑ h : Fin H,
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
      onlineRegretAnalysisCharge (H : ℝ) (Real.log (1/δ)) c₁ c₂ (stage h) U sa.1 sa.2) =
      ∑ h : Fin H, onlineCappedEpisodeT2 H stage state action (Real.log (1/δ)) c₁ c₂ h.val := by
    apply Finset.sum_congr rfl
    intro h _
    simp only [hrow, htail, onlineCappedEpisodeT2, h.isLt, dif_pos]
  have hW4 : (∑ h : Fin H,
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
      max ((onlineObservedPlanningRow (stage h) sa.1 sa.2).expectation U -
        ((E h).transition sa.1 sa.2).expectation U) 0) =
      ∑ h : Fin H, max ((onlineObservedPlanningRow (stage h) (state h.val) (action h.val)).expectation
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂ ((List.ofFn stage).drop (h.val+1))) -
        ((stage h).environment.transition (state h.val) (action h.val)).expectation
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂ ((List.ofFn stage).drop (h.val+1)))) 0 := by
    apply Finset.sum_congr rfl
    intro h _
    simp only [hrow, htail]
    rfl
  change (∑ h : Fin H,
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
      (U (mvpVarianceSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2 -
        (((E h).transition sa.1 sa.2).expectation U)^2) ≤
    2*(H : ℝ)*((∑ h : Fin H,
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
      onlineRegretAnalysisCharge (H : ℝ) (Real.log (1/δ)) c₁ c₂ (stage h) U sa.1 sa.2) + H +
      ∑ h : Fin H,
      let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
      let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
      max ((onlineObservedPlanningRow (stage h) sa.1 sa.2).expectation U -
        ((E h).transition sa.1 sa.2).expectation U) 0)
  rw [hcost, hcharge, hW4]
  change (∑ h : Fin H, ((onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂
      ((List.ofFn stage).drop (h.val+1)) (state (h.val+1)))^2 -
      ((stage h).environment.transition (state h.val) (action h.val)).expectation
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂
          ((List.ofFn stage).drop (h.val+1))) ^ 2)) ≤
    2*(H : ℝ)*((∑ h : Fin H, onlineCappedEpisodeT2 H stage state action (Real.log (1/δ)) c₁ c₂ h.val) + H +
      ∑ h : Fin H, max ((onlineObservedPlanningRow (stage h) (state h.val) (action h.val)).expectation
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂ ((List.ofFn stage).drop (h.val+1))) -
        ((stage h).environment.transition (state h.val) (action h.val)).expectation
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1/δ)) c₁ c₂ ((List.ofFn stage).drop (h.val+1)))) 0) at hb
  exact hb
end StatisticalRL.OnlineRL

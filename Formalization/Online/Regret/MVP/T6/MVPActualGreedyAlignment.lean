import Formalization.Online.Regret.MVP.T6.MVPActualVarianceDefinitions
import Formalization.Online.Regret.W1.OnlineW1ActualRowAlignment

/-! Uncompiled pathwise greedy-action alignment for the actual MVP planner. -/
namespace StatisticalRL.OnlineRL
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
noncomputable local instance t6MVPActualGreedyAlignment_mvpGreedyAlignStateEq : DecidableEq State := Classical.decEq State
noncomputable local instance t6MVPActualGreedyAlignment_mvpGreedyAlignActionEq : DecidableEq Action := Classical.decEq Action

theorem mvp_actualRow_greedyMax
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (L c₁ c₂ : ℝ) (k : Fin K) (h : Fin H) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K*H) [] path
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let stages := onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val*H))
    letI : Nonempty Action := (E h).action_nonempty
    onlineCappedBackwardQAt (H : ℝ) L c₁ c₂ stages h.val sa.1 sa.2 =
      actionMaximum (onlineCappedBackwardQAt (H : ℝ) L c₁ c₂ stages h.val sa.1) := by
  classical
  dsimp only
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K*H) [] path
  let n := k.val*H+h.val
  have hn : n < history.length := by
    have hl := onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH initial fallback planner) (K*H) [] path
    dsimp [history] at hl
    rw [hl]
    simp only [List.length_nil, zero_add]
    calc
      n < k.val*H+H := Nat.add_lt_add_left h.isLt _
      _ = (k.val+1)*H := by rw [Nat.succ_mul]
      _ ≤ K*H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  have hr := onlineSequentialEpisode_actual_row H K hH E initial fallback planner path k h
  have hs : onlineActualStageRowSequence H K hH initial fallback planner path h k.val =
      ((history.get ⟨n,hn⟩).1).2 := by
    change (onlineTranscriptRowSequence
      (onlineEpisodicChoose H K hH initial fallback planner []) history n).2 = _
    rw [onlineTranscriptRowSequence_agrees _ history ⟨n,hn⟩]
  have hrow : ((history.get ⟨n,hn⟩).1).2 =
      (onlineEpisodicCurrentState H K initial fallback (history.take n),
       planner (history.take (k.val*H)) h
         (onlineEpisodicCurrentState H K initial fallback (history.take n))) := by
    exact congrArg Prod.snd (by simpa [history,n] using hr)
  rw [hs,hrow]
  exact onlineMVPCommittedGreedyPlanner_max hH E fallback L c₁ c₂
    (history.take (k.val*H)) h _

/-- The maximizer statement in the one-stage form consumed by the fixed-table
episode bound. The list is exactly the actual pre-episode MVP table. -/
theorem mvp_actualRow_stageGreedy
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (L c₁ c₂ : ℝ) (k : Fin K) (h : Fin H) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K*H) [] path
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let stages := onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val*H))
    letI : Nonempty State := (E h).state_nonempty
    let stage := onlineMVPActualPlanningStage E
      (onlineMVPHistoryRowAt hH E fallback (history.take (k.val*H)))
      (onlineMVPHistoryNextAt fallback (history.take (k.val*H)))
      (history.take (k.val*H)).length h
    letI : Nonempty Action := (E h).action_nonempty
    onlineCappedStageQ (H : ℝ) L c₁ c₂ stage
      (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ (stages.drop (h.val+1))) sa.1 sa.2 =
      actionMaximum (onlineCappedStageQ (H : ℝ) L c₁ c₂ stage
        (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ (stages.drop (h.val+1))) sa.1) := by
  classical
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K*H) [] path
  let stages := onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val*H))
  have hi : h.val < stages.length := by
    simp [stages, onlineMVPHistoryPlanningStages, h.isLt]
  have hd : stages.drop h.val = stages[h.val]'hi :: stages.drop (h.val+1) := by
    exact List.drop_eq_getElem_cons hi
  letI : Nonempty Action := (E h).action_nonempty
  have hm := mvp_actualRow_greedyMax H K hH E initial fallback path L c₁ c₂ k h
  change onlineCappedBackwardQAt (H : ℝ) L c₁ c₂ stages h.val
      (onlineActualStageRowSequence H K hH initial fallback planner path h k.val).1
      (onlineActualStageRowSequence H K hH initial fallback planner path h k.val).2 =
    actionMaximum (onlineCappedBackwardQAt (H : ℝ) L c₁ c₂ stages h.val
      (onlineActualStageRowSequence H K hH initial fallback planner path h k.val).1) at hm
  simp only [onlineCappedBackwardQAt, hd, onlineCappedBackwardQ] at hm
  simpa [planner, history, stages, onlineMVPHistoryPlanningStages, List.getElem_ofFn] using hm
end StatisticalRL.OnlineRL

import Formalization.Online.Regret.MVP.T6.MVPActualGreedyAlignment
import Formalization.Online.Regret.MVP.T6.MVPActualRowAlignment
import Formalization.Online.Regret.MVP.T6.MVPVarianceEpisodeBudget
import Formalization.Online.Regret.T4.OnlineRegretT4ActualBridge

/-! Actual MVP played-action instantiation of the fixed-table episode bound. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance t6MVPActualEpisodeBudget_mvpEpisodeStateEq : DecidableEq State := Classical.decEq State
noncomputable local instance t6MVPActualEpisodeBudget_mvpEpisodeActionEq : DecidableEq Action := Classical.decEq Action

theorem mvp_actualEpisode_trueVariance_square_budget
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (k : Fin K) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K*H) [] path
    let prehist := history.take (k.val*H)
    let stage : Fin H → OnlineObservedPlanningStage State Action := fun h =>
      letI : Nonempty State := (E h).state_nonempty
      onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback prehist)
        (onlineMVPHistoryNextAt fallback prehist) prehist.length h
    let state := fun n => onlineEpisodicCurrentState H K initial fallback (history.take (k.val*H+n))
    let action := fun n => if hn : n < H then onlineT4PlayedAction H K hH initial fallback planner path k ⟨n,hn⟩
      else Classical.choice ((E ⟨0,hH⟩).action_nonempty)
    (∑ n ∈ Finset.range H,
      ((onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (n + 1)) (state (n + 1)))^2 -
       (if hn : n < H then ((stage ⟨n, hn⟩).environment.transition (state n) (action n)).expectation
         (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (n + 1))) else 0)^2)) ≤
    2 * (H : ℝ) * ((∑ n ∈ Finset.range H, onlineCappedEpisodeT2 H stage state action L c₁ c₂ n) + H +
      ∑ n ∈ Finset.range H, if hn : n < H then
        max ((onlineObservedPlanningRow (stage ⟨n,hn⟩) (state n) (action n)).expectation
          (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (n+1))) -
          ((stage ⟨n,hn⟩).environment.transition (state n) (action n)).expectation
          (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (n+1)))) 0 else 0) := by
  classical
  dsimp only
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K*H) [] path
  let prehist := history.take (k.val*H)
  let stage : Fin H → OnlineObservedPlanningStage State Action := fun h =>
    letI : Nonempty State := (E h).state_nonempty
    onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback prehist)
      (onlineMVPHistoryNextAt fallback prehist) prehist.length h
  let state := fun n => onlineEpisodicCurrentState H K initial fallback (history.take (k.val*H+n))
  let action := fun n => if hn : n < H then onlineT4PlayedAction H K hH initial fallback planner path k ⟨n,hn⟩
    else Classical.choice ((E ⟨0,hH⟩).action_nonempty)
  have hgreedy : ∀ h : Fin H, letI : Nonempty Action := (stage h).environment.action_nonempty
      onlineCappedStageQ (H : ℝ) L c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (h.val+1)))
        (state h.val) (action h.val) =
      actionMaximum (onlineCappedStageQ (H : ℝ) L c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ ((List.ofFn stage).drop (h.val+1))) (state h.val)) := by
    intro h
    letI : Nonempty Action := (E h).action_nonempty
    have hr := onlineSequentialEpisode_actual_row H K hH E initial fallback planner path k h
    have ha := onlineT4PlayedAction_eq_selected H K hH E initial fallback planner path k h
    have hg := mvp_actualRow_stageGreedy H K hH E initial fallback path L c₁ c₂ k h
    have hrow : onlineActualStageRowSequence H K hH initial fallback planner path h k.val =
        (state h.val, action h.val) := by
      have hsa := onlineTranscriptRowSequence_agrees
        (onlineEpisodicChoose H K hH initial fallback planner []) history
        ⟨k.val*H+h.val, by
          simp [history, onlineSequentialPathHistory_length];
          exact lt_of_lt_of_le (Nat.add_lt_add_left h.isLt _) (by nlinarith [k.isLt])⟩
      have hact : action h.val = planner (history.take (k.val*H)) h (state h.val) := by
        simpa [action, state, onlineT4EpisodeState, history, planner, h.isLt] using ha
      rw [hact]
      simpa [onlineActualStageRowSequence, hsa, state, history, planner] using congrArg Prod.snd hr
    simpa [planner, history, prehist, stage, state, action, hrow,
      onlineMVPHistoryPlanningStages, List.take_take] using hg
  exact mvp_episode_trueVariance_square_budget H stage state action L c₁ c₂ hL hc₁ hc₂ hgreedy
end StatisticalRL.OnlineRL

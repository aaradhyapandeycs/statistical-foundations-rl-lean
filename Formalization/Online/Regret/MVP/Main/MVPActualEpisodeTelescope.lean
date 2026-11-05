import Formalization.Online.Regret.MVP.T6.MVPActualEpisodeRemainder
import Formalization.Online.Regret.Telescope

/-! actual MVP episode telescope, with no optimism or tail premise. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpRegretStateEq : DecidableEq State := Classical.decEq State
noncomputable local instance mvpRegretActionEq : DecidableEq Action := Classical.decEq Action

theorem mvpActualEpisode_realized_telescope
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) (hδ : 0<δ) (hδsmall : δ≤1/100)
    (hc₁ : 4≤c₁) (hc₂ : c₁^2≤c₂) (k : Fin K) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
    let history := mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂
    let prehist := history.take (k.val*H)
    let stage := fun h : Fin H =>
      letI : Nonempty State := (E h).state_nonempty
      onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback prehist)
        (onlineMVPHistoryNextAt fallback prehist) prehist.length h
    let state := fun n => onlineEpisodicCurrentState H K initial fallback (history.take (k.val*H+n))
    let action := fun n => if hn : n < H then onlineT4PlayedAction H K hH initial fallback planner path k ⟨n,hn⟩
      else Classical.choice ((E ⟨0,hH⟩).action_nonempty)
    onlineCappedEpisodeValueAlongPath stage state H (Real.log (1/δ)) c₁ c₂ 0 ≤
      ∑ n ∈ Finset.range H, onlineCappedEpisodeTelescopeSummand H stage state action (Real.log (1/δ)) c₁ c₂ n := by
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
  exact onlineCappedEpisode_realized_telescope H stage state action δ c₁ c₂ hδ hδsmall hc₁ hc₂
    (fun h => (E h).action_nonempty) hgreedy
end StatisticalRL.OnlineRL

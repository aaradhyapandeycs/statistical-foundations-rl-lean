import Formalization.Online.Regret.MVP.Optimism.MVPBackwardOptimism
import Formalization.Online.Regret.MVP.Model.OnlineMVPActualPlanningAdapter
import Formalization.Online.Regret.MVP.MVPVarianceDefinitions
import Formalization.Online.Regret.MVP.MVPActualProfiles
import Formalization.Online.Regret.W1.OnlineW1StageEpisodeCount
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualEpisodeRankKernel

/-! Connect the observed row in the sequential transcript to the finite typed
visit-rank kernel. This is a deterministic identity under exact transcript
equality; it makes no probability claim. -/
namespace StatisticalRL.OnlineRL

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Under equality of the full transcript, the path-history planning row at
the beginning of episode `k` is the typed visit-rank kernel for the same
finite stack data. -/
theorem mvpPathPlanningRow_eq_typedRankKernel_of_transcript
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (path : OnlineOutcomePath State (K * H)) (δ c₁ c₂ : ℝ)
    (htranscript :
      onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂))
        (K * H) [] path =
      onlineMVPActualStackHistory hH initial fallback
        (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂)
        data (K * H))
    (h : Fin H) (k : Fin K) (s : State) (a : Action) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
    onlineObservedPlanningRow
        ((onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val * H))).get
          ⟨h.val, by simp [onlineMVPHistoryPlanningStages]⟩) s a =
      mvp_visitRankKernel K onlineUniformInitialRow
        (onlineMVPActualFirstVisitRow data (h, (s, a)) (by have hk := k.isLt; omega))
        (fun j => MVPUniformSource.batchRow data j h s a)
        ⟨onlineVisitCount (onlineMVPActualStackRowAt hH initial fallback planner data)
          (k.val * H) (h, (s, a)), by
            classical
            let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
            let r : Fin H × (State × Action) := (h, (s, a))
            have hrow : onlineVisitCount rowAt (k.val * H) r ≤ k.val := by
              have hstage : ∀ n, n < k.val * H → (rowAt n).1.val = n % H := by
                intro n hn
                exact onlineMVPActualStackRowAt_stage hH initial fallback planner data n
              have hcount := onlineVisitCount_stage_episode_eq rowAt h k.val hH r rfl hstage
              calc
                onlineVisitCount rowAt (k.val * H) r =
                    onlineVisitCount (fun e => rowAt (e * H + h.val)) k.val r := hcount
                _ ≤ k.val := MVPProfile.onlineVisitCount_le_prefix _ _ _
            exact lt_of_le_of_lt hrow k.isLt⟩ := by
  classical
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  have hprefix : history.take (k.val * H) =
      onlineMVPActualStackHistory hH initial fallback planner data (k.val * H) := by
    have hfull : history = onlineMVPActualStackHistory hH initial fallback planner data (K * H) := by
      simpa [history, planner] using htranscript
    rw [hfull]
    exact onlineStackHistory_take
      (onlineEpisodicChoose H K hH initial fallback planner)
      (onlineFiniteStackExtend K fallback data) (K * H) (k.val * H)
      (Nat.mul_le_mul_right H k.isLt.le)
  have hstages :
      onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val * H)) =
      List.ofFn (fun h' : Fin H =>
        onlineMVPActualPlanningStage E
          (onlineMVPActualStackRowAt hH initial fallback planner data)
          (onlineMVPActualStackNextAt hH initial fallback planner data) (k.val * H) h') := by
    rw [hprefix]
    exact onlineMVPHistoryPlanningStages_actualStack_eq hH E initial fallback planner data
      (k.val * H)
  change onlineObservedPlanningRow
      ((onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val * H))).get
        ⟨h.val, by simp [onlineMVPHistoryPlanningStages]⟩) s a = _
  have hget :
      (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val * H))).get
          ⟨h.val, by simp [onlineMVPHistoryPlanningStages]⟩ =
        onlineMVPActualPlanningStage E
          (onlineMVPActualStackRowAt hH initial fallback planner data)
          (onlineMVPActualStackNextAt hH initial fallback planner data) (k.val * H) h := by
    simp [hstages]
  rw [hget]
  exact onlineMVPActualEpisodePlanningRow_eq_typedVisitRankKernel
    hH E initial fallback planner data k h s a

end StatisticalRL.OnlineRL

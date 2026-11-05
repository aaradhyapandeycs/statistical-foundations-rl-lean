import Formalization.Online.Regret.MVP.Optimism.MVPBackwardOptimism
import Formalization.Online.Regret.MVP.MVPVarianceDefinitions
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathPlanningRowRankKernel
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathSelectedRowStackIdentity
import Formalization.Online.Regret.MVP.Decoupling.MVPVisitRankError

/-! Pointwise path-to-rank identity for the W4 summand. The only bridge input
is equality of the full sequential transcript and finite-stack transcript. -/
namespace StatisticalRL.OnlineRL

open StatisticalRL.OnlineRL.MVPUniformSource

variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def mvpPathStackRankValues
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (L c₁ c₂ : ℝ) : Fin H → Fin K → State → ℝ :=
  fun h k s => onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂
    (List.ofFn (fun h' : Fin H =>
      letI : Nonempty State := (E h').state_nonempty
      onlineMVPActualPlanningStage E
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data) (k.val * H) h'))
    (h.val + 1) s

/-- At a fixed stage/episode, the actual path's positive W4 term is precisely
the finite typed-rank positive error at the same observed state-action row. -/
theorem mvpVarianceW4_term_eq_rankError_of_transcript
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
    (h : Fin H) (k : Fin K) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
    letI : Nonempty State := (E h).state_nonempty
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
    let u := onlineVisitCount rowAt (k.val * H) (h, sa)
    let V := mvpPathStackRankValues hH E initial fallback planner data
      (Real.log (1 / δ)) c₁ c₂
    max ((onlineObservedPlanningRow
      (onlineMVPActualPlanningStage E
        (onlineMVPHistoryRowAt hH E fallback
          ((mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val * H)))
        (onlineMVPHistoryNextAt fallback
          ((mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val * H)))
        ((mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val * H)).length h)
      sa.1 sa.2).expectation (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k) -
      ((E h).transition sa.1 sa.2).expectation
        (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k)) 0 =
      mvp_rankPositiveError K ((E h).transition sa.1 sa.2) onlineUniformInitialRow
        (onlineMVPActualFirstVisitRow data (h, sa) (by have hk := k.isLt; omega))
        (fun j => MVPUniformSource.batchRow data j h sa.1 sa.2) u (V h k) := by
  classical
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
  letI : Nonempty State := (E h).state_nonempty
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let u := onlineVisitCount rowAt (k.val * H) (h, sa)
  let V := mvpPathStackRankValues hH E initial fallback planner data (Real.log (1 / δ)) c₁ c₂
  let hist := history.take (k.val * H)
  let stage := onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
    (onlineMVPHistoryNextAt fallback hist) hist.length h
  let stackStage := onlineMVPActualPlanningStage E
    (onlineMVPActualStackRowAt hH initial fallback planner data)
    (onlineMVPActualStackNextAt hH initial fallback planner data) (k.val * H) h
  let q := onlineObservedPlanningRow stage sa.1 sa.2
  let p := (E h).transition sa.1 sa.2
  have hprefix : hist = onlineMVPActualStackHistory hH initial fallback planner data (k.val * H) := by
    have hstack : history.take (k.val * H) =
        (onlineMVPActualStackHistory hH initial fallback planner data (K * H)).take (k.val * H) := by
      simpa [history, planner] using congrArg (fun xs => xs.take (k.val * H)) htranscript
    calc
      hist = (onlineMVPActualStackHistory hH initial fallback planner data (K * H)).take
          (k.val * H) := hstack
      _ = onlineMVPActualStackHistory hH initial fallback planner data (k.val * H) := by
        simpa [onlineMVPActualStackHistory] using
          onlineStackHistory_take
            (onlineEpisodicChoose H K hH initial fallback planner)
            (onlineFiniteStackExtend K fallback data) (K * H) (k.val * H)
            (Nat.mul_le_mul_right H k.isLt.le)
  have hstages :
      onlineMVPHistoryPlanningStages hH E fallback hist =
      List.ofFn (fun h' : Fin H => onlineMVPActualPlanningStage E
        (onlineMVPActualStackRowAt hH initial fallback planner data)
        (onlineMVPActualStackNextAt hH initial fallback planner data) (k.val * H) h') := by
    rw [hprefix]
    exact onlineMVPHistoryPlanningStages_actualStack_eq hH E initial fallback planner data
      (k.val * H)
  have hvalue : mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k = V h k := by
    change onlineCappedBackwardValueAt (H : ℝ) (Real.log (1 / δ)) c₁ c₂
        (onlineMVPHistoryPlanningStages hH E fallback hist) (h.val + 1) =
      onlineCappedBackwardValueAt (H : ℝ) (Real.log (1 / δ)) c₁ c₂
        (List.ofFn (fun h' : Fin H =>
          letI : Nonempty State := (E h').state_nonempty
          onlineMVPActualPlanningStage E
            (onlineMVPActualStackRowAt hH initial fallback planner data)
            (onlineMVPActualStackNextAt hH initial fallback planner data) (k.val * H) h'))
        (h.val + 1)
    rw [hstages]
  have hsa : sa = (rowAt (k.val * H + h.val)).2 := by
    exact mvpPathSelectedRow_eq_stackRow_of_transcript hH E initial fallback planner data
      path htranscript h k
  have hu : u < K := by
    dsimp [u, rowAt]
    let rankRows := onlineMVPActualStackRowAt hH initial fallback planner data
    have hstageCount : ∀ n, n < k.val * H → (rankRows n).1.val = n % H := by
      intro n hn
      exact onlineMVPActualStackRowAt_stage hH initial fallback planner data n
    have hcount := onlineVisitCount_stage_episode_eq rankRows h k.val hH
      (h, sa) rfl hstageCount
    calc
      onlineVisitCount rankRows (k.val * H) (h, sa) =
          onlineVisitCount (fun e => rankRows (e * H + h.val)) k.val (h, sa) := hcount
      _ ≤ k.val := MVPProfile.onlineVisitCount_le_prefix _ _ _
      _ < K := k.isLt
  have hrow : q = mvp_visitRankKernel K onlineUniformInitialRow
      (onlineMVPActualFirstVisitRow data (h, sa) (by have hk := k.isLt; omega))
      (fun j => MVPUniformSource.batchRow data j h sa.1 sa.2)
      ⟨u, hu⟩ := by
    have hkernel := mvpPathPlanningRow_eq_typedRankKernel_of_transcript
      hH E initial fallback data path δ c₁ c₂ htranscript h k sa.1 sa.2
    simpa [q, stage, hist, history, planner, u, rowAt, onlineMVPHistoryPlanningStages] using hkernel
  change max (q.expectation
      (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k) -
      p.expectation (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k)) 0 =
    mvp_rankPositiveError K p onlineUniformInitialRow
      (onlineMVPActualFirstVisitRow data (h, sa) (by have hk := k.isLt; omega))
      (fun j => MVPUniformSource.batchRow data j h sa.1 sa.2) u (V h k)
  rw [hvalue, hrow]
  simp [mvp_rankPositiveError, dif_pos hu, mvp_rowPositiveError]

end StatisticalRL.OnlineRL

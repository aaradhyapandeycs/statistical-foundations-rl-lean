import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathW3T6RankSum
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathPlanningRowRankKernel
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualTypedRankKernel

/-! Pointwise signed squared-error comparison with the nonnegative rank error. -/
namespace StatisticalRL.OnlineRL

open StatisticalRL.OnlineRL.MVPUniformSource

variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualW3_term_le_rankSquareError_of_transcript
    {H K : ℕ} (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (data : OnlineMDPRow State Action H × Fin K → State)
    (path : OnlineOutcomePath State (K * H)) (δ c₁ c₂ : ℝ)
    (htranscript :
      onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂))
        (K * H) [] path =
      onlineMVPActualStackHistory hH initial fallback
        (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂)
        data (K * H)) (h : Fin H) (k : Fin K) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let hist := (mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val * H)
    letI : Nonempty State := (E h).state_nonempty
    let stage := onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
      (onlineMVPHistoryNextAt fallback hist) hist.length h
    let u := onlineVisitCount (onlineMVPActualStackRowAt hH initial fallback planner data)
      (k.val * H) (h, sa)
    let V := mvpPathStackRankValues hH E initial fallback planner data (Real.log (1 / δ)) c₁ c₂
    (onlineObservedPlanningRow stage sa.1 sa.2).expectation
        (fun s => (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k s)^2) -
      ((E h).transition sa.1 sa.2).expectation
        (fun s => (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k s)^2) ≤
    mvp_rankPositiveError K ((E h).transition sa.1 sa.2) onlineUniformInitialRow
      (onlineMVPActualFirstVisitRow data (h, sa) hK)
      (fun j => MVPUniformSource.batchRow data j h sa.1 sa.2) u (fun s => (V h k s)^2) := by
  classical
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let hist := (mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val * H)
  letI : Nonempty State := (E h).state_nonempty
  let stage := onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
    (onlineMVPHistoryNextAt fallback hist) hist.length h
  let rowAt := onlineMVPActualStackRowAt hH initial fallback planner data
  let u := onlineVisitCount rowAt (k.val * H) (h, sa)
  let V := mvpPathStackRankValues hH E initial fallback planner data (Real.log (1 / δ)) c₁ c₂
  let q := onlineObservedPlanningRow stage sa.1 sa.2
  let p := (E h).transition sa.1 sa.2
  have hu : u < K := by
    dsimp [u, rowAt]
    let rankRows := onlineMVPActualStackRowAt hH initial fallback planner data
    have hstageCount : ∀ n, n < k.val * H → (rankRows n).1.val = n % H := by
      intro n hn
      exact onlineMVPActualStackRowAt_stage hH initial fallback planner data n
    have hcount := onlineVisitCount_stage_episode_eq rankRows h k.val hH (h, sa) rfl hstageCount
    calc
      onlineVisitCount rankRows (k.val * H) (h, sa) =
          onlineVisitCount (fun e => rankRows (e * H + h.val)) k.val (h, sa) := hcount
      _ ≤ k.val := MVPProfile.onlineVisitCount_le_prefix _ _ _
      _ < K := k.isLt
  have hrow : q = mvp_visitRankKernel K onlineUniformInitialRow
      (onlineMVPActualFirstVisitRow data (h, sa) hK)
      (fun j => MVPUniformSource.batchRow data j h sa.1 sa.2) ⟨u, hu⟩ := by
    have hkernel := mvpPathPlanningRow_eq_typedRankKernel_of_transcript
      hH E initial fallback data path δ c₁ c₂ htranscript h k sa.1 sa.2
    simpa [q, stage, hist, planner, u, rowAt, mvpVarianceHistory,
      onlineMVPHistoryPlanningStages] using hkernel
  have hv := mvpVarianceContinuation_eq_pathRankValue_of_transcript
    hH E initial fallback data path δ c₁ c₂ htranscript h k
  have hsigned : q.expectation (fun s => (mvpVarianceContinuation
      H K hH E initial fallback path δ c₁ c₂ h k s)^2) -
      p.expectation (fun s => (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k s)^2) ≤
      max (q.expectation (fun s => (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k s)^2) -
        p.expectation (fun s => (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k s)^2)) 0 :=
    le_max_left _ _
  have hmax : max (q.expectation (fun s => (mvpVarianceContinuation
      H K hH E initial fallback path δ c₁ c₂ h k s)^2) -
      p.expectation (fun s => (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k s)^2)) 0 =
      mvp_rankPositiveError K p onlineUniformInitialRow
        (onlineMVPActualFirstVisitRow data (h, sa) hK)
        (fun j => MVPUniformSource.batchRow data j h sa.1 sa.2) u (fun s => (V h k s)^2) := by
    rw [hrow, hv]
    simp [mvp_rankPositiveError, dif_pos hu, mvp_rowPositiveError, V, planner,
      mvpPathStackRankValues]
  simpa [q, p, sa, stage, hist, planner, u, rowAt, V] using hsigned.trans_eq hmax

end StatisticalRL.OnlineRL

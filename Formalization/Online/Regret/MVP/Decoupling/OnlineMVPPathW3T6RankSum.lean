import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathRankSumIdentity
import Formalization.Online.Regret.MVP.Decoupling.MVPRankErrorSourceBounds
import Formalization.Online.Regret.MVP.MVPT5Definitions

/-! Path/stack bridges for the squared empirical error and predictable
variance. The only path input is exact transcript equality. -/
namespace StatisticalRL.OnlineRL

open scoped BigOperators
open StatisticalRL.OnlineRL.MVPUniformSource

variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpVarianceContinuation_eq_pathRankValue_of_transcript
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
        data (K * H)) (h : Fin H) (k : Fin K) :
    mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k =
      mvpPathStackRankValues hH E initial fallback
        (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂)
        data (Real.log (1 / δ)) c₁ c₂ h k := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  have hprefix : history.take (k.val * H) =
      onlineMVPActualStackHistory hH initial fallback planner data (k.val * H) := by
    have hstack : history.take (k.val * H) =
        (onlineMVPActualStackHistory hH initial fallback planner data (K * H)).take (k.val * H) := by
      simpa [history, planner] using congrArg (fun xs => xs.take (k.val * H)) htranscript
    calc
      _ = (onlineMVPActualStackHistory hH initial fallback planner data (K * H)).take
          (k.val * H) := hstack
      _ = onlineMVPActualStackHistory hH initial fallback planner data (k.val * H) := by
        simpa [onlineMVPActualStackHistory] using
          onlineStackHistory_take
            (onlineEpisodicChoose H K hH initial fallback planner)
            (onlineFiniteStackExtend K fallback data) (K * H) (k.val * H)
            (Nat.mul_le_mul_right H k.isLt.le)
  have hstages :
      onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val * H)) =
        List.ofFn (fun h' : Fin H =>
          letI : Nonempty State := (E h').state_nonempty
          onlineMVPActualPlanningStage E
            (onlineMVPActualStackRowAt hH initial fallback planner data)
            (onlineMVPActualStackNextAt hH initial fallback planner data) (k.val * H) h') := by
    rw [hprefix]
    exact onlineMVPHistoryPlanningStages_actualStack_eq hH E initial fallback planner data
      (k.val * H)
  change onlineCappedBackwardValueAt (H : ℝ) (Real.log (1 / δ)) c₁ c₂
      (onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val * H))) (h.val + 1) =
    onlineCappedBackwardValueAt (H : ℝ) (Real.log (1 / δ)) c₁ c₂
      (List.ofFn (fun h' : Fin H =>
        letI : Nonempty State := (E h').state_nonempty
        onlineMVPActualPlanningStage E
          (onlineMVPActualStackRowAt hH initial fallback
            (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂) data)
          (onlineMVPActualStackNextAt hH initial fallback
            (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂) data)
          (k.val * H) h')) (h.val + 1)
  simpa [history, planner] using congrArg
    (fun stages => onlineCappedBackwardValueAt (H : ℝ) (Real.log (1 / δ)) c₁ c₂
      stages (h.val + 1)) hstages

noncomputable def mvpPathRankTransition {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) :
    Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
  fun _ r => (E r.1).transition r.2.1 r.2.2

theorem mvpVarianceT6_eq_pathRankVarianceTotal_of_transcript
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
        data (K * H)) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
    let rows := mvpPathRankRows hH initial fallback planner data
    let V := mvpPathStackRankValues hH E initial fallback planner data (Real.log (1 / δ)) c₁ c₂
    let p := mvpPathRankTransition E
    mvpVarianceT6UCB H K hH E initial fallback path δ c₁ c₂ =
      ∑ h : Fin H, ∑ k : Fin K, (p h (rows h k.val)).variance (V h k) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
  let rows := mvpPathRankRows hH initial fallback planner data
  let V := mvpPathStackRankValues hH E initial fallback planner data (Real.log (1 / δ)) c₁ c₂
  let p := mvpPathRankTransition E
  change mvpVarianceT6UCB H K hH E initial fallback path δ c₁ c₂ =
    ∑ h : Fin H, ∑ k : Fin K, (p h (rows h k.val)).variance (V h k)
  unfold mvpVarianceT6UCB
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let r := onlineMVPActualStackRowAt hH initial fallback planner data (k.val * H + h.val)
  have hsa : sa = r.2 :=
    mvpPathSelectedRow_eq_stackRow_of_transcript hH E initial fallback planner data
      path htranscript h k
  have htag : r.1 = h := by
    apply Fin.ext
    have hs := onlineMVPActualStackRowAt_stage hH initial fallback planner data
      (k.val * H + h.val)
    dsimp [r]
    rw [hs, Nat.mul_comm k.val H, Nat.add_comm (H * k.val) h.val,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
  have hr : r = (h, sa) := Prod.ext htag hsa.symm
  have hrows : rows h k.val = (h, sa) := by
    change r = (h, sa)
    exact hr
  have hv := mvpVarianceContinuation_eq_pathRankValue_of_transcript
    hH E initial fallback data path δ c₁ c₂ htranscript h k
  rw [hv]
  change ((E h).transition sa.1 sa.2).variance
      (mvpPathStackRankValues hH E initial fallback planner data (Real.log (1 / δ)) c₁ c₂ h k) =
    ((E (rows h k.val).1).transition (rows h k.val).2.1 (rows h k.val).2.2).variance
      (mvpPathStackRankValues hH E initial fallback planner data (Real.log (1 / δ)) c₁ c₂ h k)
  rw [hrows]

end StatisticalRL.OnlineRL

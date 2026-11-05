import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathPairRankTransport
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathW3AggregateRank

/-! Signed W3 is bounded by the corresponding pair-carrier square error. -/
namespace StatisticalRL.OnlineRL

open scoped BigOperators
open StatisticalRL.OnlineRL.MVPUniformSource

variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualW3_le_pairRankErrorSquare_of_transcript
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
    let rows := mvpPathPairRankRows hH initial fallback planner data
    let V := mvpPathPairRankValues hH E initial fallback planner data
      (Real.log (1 / δ)) c₁ c₂
    let p := mvpPathPairRankTransition E
    let q0 := mvpPathPairRankInitial hH E
    let q1 := mvpPathPairRankFirst (by omega) data
    let qb := mvpPathPairRankBatch data
    mvpActualW3 H K hH E initial fallback path δ c₁ c₂ ≤
      mvp_rankErrorTotal rows K (fun h k s => (V h k s)^2) p q0 q1 qb := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
  let rowsTag := mvpPathRankRows hH initial fallback planner data
  let rows := mvpPathPairRankRows hH initial fallback planner data
  let VTag := mvpPathStackRankValues hH E initial fallback planner data
    (Real.log (1 / δ)) c₁ c₂
  let V := mvpPathPairRankValues hH E initial fallback planner data
    (Real.log (1 / δ)) c₁ c₂
  let pTag : Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
    fun _ r => (E r.1).transition r.2.1 r.2.2
  let q0Tag : Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
    fun _ _ => onlineUniformInitialRow
  let q1Tag : Fin H → OnlineMDPRow State Action H → FiniteDistribution State :=
    fun _ r => onlineMVPActualFirstVisitRow data r hK
  let qbTag : Fin H → OnlineMDPRow State Action H → Fin (Nat.log2 K) → FiniteDistribution State :=
    fun _ r j => MVPUniformSource.batchRow data j r.1 r.2.1 r.2.2
  let p := mvpPathPairRankTransition E
  let q0 := mvpPathPairRankInitial hH E
  let q1 := mvpPathPairRankFirst hK data
  let qb := mvpPathPairRankBatch data
  have hrowsAll (h : Fin H) (n : ℕ) : rowsTag h n = (h, rows h n) := by
    apply Prod.ext
    · apply Fin.ext
      have hs := onlineMVPActualStackRowAt_stage hH initial fallback planner data
        (n * H + h.val)
      dsimp [rowsTag, mvpPathRankRows]
      rw [hs, Nat.mul_comm n H, Nat.add_comm (H * n) h.val,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.isLt]
    · rfl
  have hrowsFn (h : Fin H) : rowsTag h = fun n => (h, rows h n) :=
    funext (hrowsAll h)
  have hvalues (h : Fin H) (k : Fin K) : VTag h k = V h k := rfl
  have hfull := mvpActualW3_le_rankErrorTotal_square_of_transcript
    hH hK E initial fallback data path δ c₁ c₂ htranscript
  change mvpActualW3 H K hH E initial fallback path δ c₁ c₂ ≤
    mvp_rankErrorTotal rowsTag K (fun h k s => (VTag h k s)^2)
      pTag q0Tag q1Tag qbTag at hfull
  have hreplaceRows :
      mvp_rankErrorTotal rowsTag K (fun h k s => (VTag h k s)^2)
        pTag q0Tag q1Tag qbTag =
      mvp_rankErrorTotal (fun h n => (h, rows h n)) K
        (fun h k s => (VTag h k s)^2) pTag q0Tag q1Tag qbTag := by
    unfold mvp_rankErrorTotal
    apply Finset.sum_congr rfl
    intro h _
    rw [hrowsFn h]
  have htransport := mvp_rankErrorTotal_tagMap_eq rows K
    (fun h r => (h, r)) (by
      intro h a b hab
      exact congrArg Prod.snd hab)
    (fun h k s => (VTag h k s)^2) pTag q0Tag q1Tag qbTag
  have htransport' :
      mvp_rankErrorTotal (fun h n => (h, rows h n)) K
        (fun h k s => (VTag h k s)^2) pTag q0Tag q1Tag qbTag =
      mvp_rankErrorTotal rows K (fun h k s => (VTag h k s)^2)
        (fun h r => pTag h (h, r))
        (fun h r => q0Tag h (h, r))
        (fun h r => q1Tag h (h, r))
        (fun h r j => qbTag h (h, r) j) := htransport
  have hproviders :
      mvp_rankErrorTotal rows K (fun h k s => (VTag h k s)^2)
        (fun h r => pTag h (h, r))
        (fun h r => q0Tag h (h, r))
        (fun h r => q1Tag h (h, r))
        (fun h r j => qbTag h (h, r) j) =
      mvp_rankErrorTotal rows K (fun h k s => (V h k s)^2) p q0 q1 qb := by
    unfold mvp_rankErrorTotal
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro k _
    dsimp
    rw [hvalues h k]
    simp [pTag, p, q0Tag, q0, q1Tag, q1, qbTag, qb,
      mvpPathPairRankTransition, mvpPathPairRankInitial, mvpPathPairRankFirst,
      onlineMVPActualFirstVisitRow]
    rfl
  calc
    mvpActualW3 H K hH E initial fallback path δ c₁ c₂ ≤
        mvp_rankErrorTotal rowsTag K (fun h k s => (VTag h k s)^2)
          pTag q0Tag q1Tag qbTag := hfull
    _ = mvp_rankErrorTotal rows K (fun h k s => (V h k s)^2) p q0 q1 qb := by
      rw [hreplaceRows, htransport', hproviders]

end StatisticalRL.OnlineRL

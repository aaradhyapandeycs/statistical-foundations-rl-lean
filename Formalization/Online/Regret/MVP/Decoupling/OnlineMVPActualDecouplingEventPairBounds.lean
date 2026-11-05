import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathPairW3Transport
import Formalization.Online.Regret.MVP.Decoupling.MVPDecouplingFirstInequality

/-! Deterministic composition of the pair-carrier rank bounds with the
source-facing W4/T6/W3 event. No probability statement is made here. -/
namespace StatisticalRL.OnlineRL

open scoped BigOperators

variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualDecouplingEvent_of_pairRankBounds
    {H K : ℕ} (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (data : OnlineMDPRow State Action H × Fin K → State)
    (path : OnlineOutcomePath State (K * H)) (δplan c₁ c₂ I : ℝ)
    (htranscript :
      onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δplan)) c₁ c₂))
        (K * H) [] path =
      onlineMVPActualStackHistory hH initial fallback
        (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δplan)) c₁ c₂)
        data (K * H))
    (hlinear :
      let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δplan)) c₁ c₂
      let rows := mvpPathPairRankRows hH initial fallback planner data
      let V := mvpPathPairRankValues hH E initial fallback planner data
        (Real.log (1 / δplan)) c₁ c₂
      let p := mvpPathPairRankTransition E
      let q0 := mvpPathPairRankInitial hH E
      let q1 := mvpPathPairRankFirst (by omega) data
      let qb := mvpPathPairRankBatch data
      let d := (Fintype.card State : ℝ) * Fintype.card Action * H
      let T := ∑ h : Fin H, ∑ k : Fin K, (p h (rows h k.val)).variance (V h k)
      mvp_rankErrorTotal rows K V p q0 q1 qb ≤ Real.sqrt (d * I * T) + d * H * I)
    (hsquare :
      let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δplan)) c₁ c₂
      let rows := mvpPathPairRankRows hH initial fallback planner data
      let V := mvpPathPairRankValues hH E initial fallback planner data
        (Real.log (1 / δplan)) c₁ c₂
      let p := mvpPathPairRankTransition E
      let q0 := mvpPathPairRankInitial hH E
      let q1 := mvpPathPairRankFirst (by omega) data
      let qb := mvpPathPairRankBatch data
      let d := (Fintype.card State : ℝ) * Fintype.card Action * H
      mvp_rankErrorTotal rows K (fun h k s => (V h k s)^2) p q0 q1 qb ≤
        Real.sqrt (d * (H : ℝ)^2 * I *
          (∑ h : Fin H, ∑ k : Fin K, (p h (rows h k.val)).variance (V h k))) +
          d * (H : ℝ)^2 * I) :
    ((initial, path) ∈ mvpActualDecouplingEvent H K hH E fallback δplan c₁ c₂ I) := by
  classical
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δplan)) c₁ c₂
  let rows := mvpPathPairRankRows hH initial fallback planner data
  let V := mvpPathPairRankValues hH E initial fallback planner data
    (Real.log (1 / δplan)) c₁ c₂
  let p := mvpPathPairRankTransition E
  let q0 := mvpPathPairRankInitial hH E
  let q1 := mvpPathPairRankFirst hK data
  let qb := mvpPathPairRankBatch data
  let d := (Fintype.card State : ℝ) * Fintype.card Action * H
  let T := ∑ h : Fin H, ∑ k : Fin K, (p h (rows h k.val)).variance (V h k)
  have hlinear' : mvp_rankErrorTotal rows K V p q0 q1 qb ≤
      Real.sqrt (d * I * T) + d * H * I := hlinear
  have hsquare' : mvp_rankErrorTotal rows K (fun h k s => (V h k s)^2) p q0 q1 qb ≤
      Real.sqrt (d * (H : ℝ)^2 * I * T) + d * (H : ℝ)^2 * I := hsquare
  have hW4 := mvpActualW4_eq_pairRankError_of_transcript
    hH hK E initial fallback data path δplan c₁ c₂ htranscript
  have hT6 := mvpVarianceT6_eq_pairRankVariance_of_transcript
    hH hK E initial fallback data path δplan c₁ c₂ htranscript
  have hW3 := mvpActualW3_le_pairRankErrorSquare_of_transcript
    hH hK E initial fallback data path δplan c₁ c₂ htranscript
  have hT1 := mvpActualT1_le_W4 H K hH E initial fallback path δplan c₁ c₂
  change (mvpActualT1 H K hH E initial fallback path δplan c₁ c₂ ≤
      mvpVarianceW4 H K hH E initial fallback path δplan c₁ c₂) ∧
    (mvpVarianceW4 H K hH E initial fallback path δplan c₁ c₂ ≤
      Real.sqrt (d * I * mvpVarianceT6UCB H K hH E initial fallback path δplan c₁ c₂) +
        d * H * I) ∧
    (mvpActualW3 H K hH E initial fallback path δplan c₁ c₂ ≤
      Real.sqrt (d * (H : ℝ)^2 * I * mvpVarianceT6UCB H K hH E initial fallback path δplan c₁ c₂) +
        d * (H : ℝ)^2 * I)
  refine ⟨hT1, ?_, ?_⟩
  · rw [hW4, hT6]
    exact hlinear'
  · rw [hT6]
    exact hW3.trans hsquare'

end StatisticalRL.OnlineRL

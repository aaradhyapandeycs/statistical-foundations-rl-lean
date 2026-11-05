import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualRankBoundsStackProbability
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPPathPairRankTransport

/-! Convert the existing actual stack rank event to the State×Action pair
carrier used by the pathwise W4/T6/W3 transport. -/
namespace StatisticalRL.OnlineRL

open scoped BigOperators

variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualRankBoundsStackEvent_pairBounds
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (δ c₁ c₂ : ℝ)
    (sample : (Fin K → State) × (OnlineMDPRow State Action H × Fin K → State))
    (hgood : sample ∈ mvpActualRankBoundsStackEvent hH hK E fallback δ c₁ c₂) :
    let δp := onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K
    let L := Real.log (1 / δp)
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
    let rows := mvpPathPairRankRows hH sample.1 fallback planner sample.2
    let V := mvpPathPairRankValues hH E sample.1 fallback planner sample.2 L c₁ c₂
    let p := mvpPathPairRankTransition E
    let q0 := mvpPathPairRankInitial hH E
    let q1 := mvpPathPairRankFirst (by omega) sample.2
    let qb := mvpPathPairRankBatch sample.2
    let d := (Fintype.card State : ℝ) * Fintype.card Action * H
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card (Fin H × (State × Action)))) * L
    (mvp_rankErrorTotal rows K V p q0 q1 qb ≤ Real.sqrt (d * I *
      (∑ h : Fin H, ∑ k : Fin K, (p h (rows h k.val)).variance (V h k))) + d * H * I) ∧
    (mvp_rankErrorTotal rows K (fun h k s => (V h k s)^2) p q0 q1 qb ≤
      Real.sqrt (d * (H : ℝ)^2 * I *
        (∑ h : Fin H, ∑ k : Fin K, (p h (rows h k.val)).variance (V h k))) + d * (H : ℝ)^2 * I) := by
  classical
  let δp := onlineSourceOptimismDeltaPrime δ
    (Fintype.card State) (Fintype.card Action) H K
  let L := Real.log (1 / δp)
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
  let rows := mvpPathPairRankRows hH sample.1 fallback planner sample.2
  let V := mvpPathPairRankValues hH E sample.1 fallback planner sample.2 L c₁ c₂
  let p := mvpPathPairRankTransition E
  let q0 := mvpPathPairRankInitial hH E
  let q1 := mvpPathPairRankFirst (by omega) sample.2
  let qb := mvpPathPairRankBatch sample.2
  let d := (Fintype.card State : ℝ) * Fintype.card Action * H
  let I := 40000 * (Real.log K / Real.log 2)^3 *
    Real.log (3 * (Fintype.card (Fin H × (State × Action)))) * L
  let rowsActual := mvpActualRankRows hH sample.1 fallback planner sample.2
  let VActual := mvpActualRankValues hH E sample.1 fallback planner sample.2 L c₁ c₂
  let pActual := mvpActualRankTransition E
  let q0Actual := mvpActualRankInitial E hH
  let q1Actual := mvpActualRankFirst (by omega) sample.2
  let qbActual := mvpActualRankBatch sample.2
  let dActual := (Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action)
  have hd : dActual = d := by
    dsimp [dActual, d]
    simp [Fintype.card_prod, Fintype.card_fin]
    ring
  have hrows : rowsActual = rows := rfl
  have hvalues : VActual = V := rfl
  have hp : pActual = p := rfl
  have hq0 : q0Actual = q0 := rfl
  have hq1 : q1Actual = q1 := rfl
  have hqb : qbActual = qb := rfl
  have hT :
      (∑ h : Fin H, ∑ k : Fin K,
        (pActual h (rowsActual h k.val)).variance (VActual h k)) =
      ∑ h : Fin H, ∑ k : Fin K, (p h (rows h k.val)).variance (V h k) := by
    simp [hrows, hvalues, hp]
  have hgood' :
      (mvp_rankErrorTotal rowsActual K VActual pActual q0Actual q1Actual qbActual ≤
        Real.sqrt (dActual * I *
          (∑ h : Fin H, ∑ k : Fin K,
            (pActual h (rowsActual h k.val)).variance (VActual h k))) +
          dActual * H * I) ∧
      (mvp_rankErrorTotal rowsActual K (fun h k s => (VActual h k s)^2)
        pActual q0Actual q1Actual qbActual ≤
        Real.sqrt (dActual * (H : ℝ)^2 * I *
          (∑ h : Fin H, ∑ k : Fin K,
            (pActual h (rowsActual h k.val)).variance (VActual h k))) +
          dActual * (H : ℝ)^2 * I) := by
    change _ ∧ _ at hgood
    exact hgood
  simpa only [hrows, hvalues, hp, hq0, hq1, hqb, hd, hT] using hgood'

end StatisticalRL.OnlineRL

import Formalization.Online.Regret.MVP.MVPT5Definitions

/-! Definition-only actual sequential MVP empirical errors and the full
Lemma5.14 event. These definitions make no probability or proof claim. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Signed T1 uses the same retained model, continuation and played row as W4. -/
noncomputable def mvpActualT1 (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δplan c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δplan)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let hist := (mvpVarianceHistory H K hH E initial fallback path δplan c₁ c₂).take (k.val*H)
    letI : Nonempty State := (E h).state_nonempty
    let stage := onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
      (onlineMVPHistoryNextAt fallback hist) hist.length h
    let U := mvpVarianceContinuation H K hH E initial fallback path δplan c₁ c₂ h k
    ((onlineObservedPlanningRow stage sa.1 sa.2).expectation U -
      ((E h).transition sa.1 sa.2).expectation U)

/-- Full three-clause decoupling event, with a fixed planner confidence
parameter δplan and explicit source iota I. The source wrapper supplies their
corrected values before the sample is drawn. -/
noncomputable def mvpActualDecouplingEvent (H K : ℕ) (hH : 0<H)
    (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (δplan c₁ c₂ I : ℝ) : Set ((Fin K → State) × OnlineOutcomePath State (K*H)) :=
  {sample |
    let d := (Fintype.card State:ℝ)*Fintype.card Action*H
    let T6 := mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δplan c₁ c₂
    let W4 := mvpVarianceW4 H K hH E sample.1 fallback sample.2 δplan c₁ c₂
    (mvpActualT1 H K hH E sample.1 fallback sample.2 δplan c₁ c₂ ≤ W4) ∧
      (W4 ≤ Real.sqrt (d*I*T6)+d*(H:ℝ)*I) ∧
      (mvpActualW3 H K hH E sample.1 fallback sample.2 δplan c₁ c₂ ≤
        Real.sqrt (d*(H:ℝ)^2*I*T6)+d*(H:ℝ)^2*I)}

end StatisticalRL.OnlineRL

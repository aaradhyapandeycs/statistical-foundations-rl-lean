import Formalization.Online.Regret.MVP.MVPVarianceDefinitions

/-! Actual retained-table squared empirical error. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def mvpActualW3 (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let hist := (mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val*H)
    letI : Nonempty State := (E h).state_nonempty
    let stage := onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
      (onlineMVPHistoryNextAt fallback hist) hist.length h
    let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
    (onlineObservedPlanningRow stage sa.1 sa.2).expectation (fun s => (U s)^2) -
      ((E h).transition sa.1 sa.2).expectation (fun s => (U s)^2)


end StatisticalRL.OnlineRL

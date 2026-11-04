import Formalization.Online.Regret.MVP.MVPVarianceDefinitions

/-! Definitions for actual MVP retained-count and empirical variance sums. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpT2DefsStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpT2DefsActionDecidable : DecidableEq Action := Classical.decEq Action

noncomputable def mvpT2ActualRetainedCount
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K*H)) (h : Fin H) (k : Fin K) : ℕ :=
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose (K*H) [] path
  let hist := history.take (k.val*H)
  let rows := onlineActualStageRowSequence H K hH initial fallback planner path h
  letI : Nonempty State := (E h).state_nonempty
  ((onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
    (onlineMVPHistoryNextAt fallback hist) hist.length h).observations
    (rows k.val).1 (rows k.val).2).length


noncomputable def mvpActualT5 (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let hist := (mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val*H)
    letI : Nonempty State := (E h).state_nonempty
    let stage := onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
      (onlineMVPHistoryNextAt fallback hist) hist.length h
    (onlineObservedPlanningRow stage sa.1 sa.2).variance
      (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k)

end StatisticalRL.OnlineRL

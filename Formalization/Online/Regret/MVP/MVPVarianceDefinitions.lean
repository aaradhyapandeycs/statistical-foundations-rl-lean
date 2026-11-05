import Formalization.Online.Regret.MVP.MVPModelDefinitions
import Formalization.Online.Regret.Definitions
import Formalization.Online.Regret.W1.W1Definitions

/-! Actual-path definitions for the MVP variance chain.
All four sums use the same sequential outcome path, source retained-batch
planner and completed-history table. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def mvpVarianceHistory (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) :=
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
  onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K*H) [] path

noncomputable def mvpVarianceContinuation (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ)
    (h : Fin H) (k : Fin K) : State → ℝ :=
  onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δ)) c₁ c₂
    (onlineMVPHistoryPlanningStages hH E fallback
      ((mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val*H))) (h.val+1)

noncomputable def mvpVarianceT6UCB (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    ((E h).transition sa.1 sa.2).variance
      (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k)

noncomputable def mvpVarianceT2 (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let hist := (mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val*H)
    letI : Nonempty State := (E h).state_nonempty
    let stage := onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
      (onlineMVPHistoryNextAt fallback hist) hist.length h
    onlineRegretAnalysisCharge (H : ℝ) (Real.log (1/δ)) c₁ c₂ stage
      (mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k) sa.1 sa.2

noncomputable def mvpVarianceW4 (H K : ℕ) (hH : 0 < H)
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
    max ((onlineObservedPlanningRow stage sa.1 sa.2).expectation U -
      ((E h).transition sa.1 sa.2).expectation U) 0

end StatisticalRL.OnlineRL

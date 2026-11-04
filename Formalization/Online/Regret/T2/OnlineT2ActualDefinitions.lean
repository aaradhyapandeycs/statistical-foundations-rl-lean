import Formalization.Online.Regret.W1.W1Definitions

/-! Actual-history T₂ and empirical T₅ quantities. Corrected first visits use
`onlineRegretAnalysisCharge`; no concentration assumption occurs here. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance t2ActualStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t2ActualActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Empirical transition variance of the actual pre-episode optimistic tail,
summed along the same realized selected stage-state-action path. -/
noncomputable def onlineActualT5
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
    (onlineObservedPlanningRow stage sa.1 sa.2).variance U

/-- T₂ is the sum of the actual trajectory's already-defined second component. -/
noncomputable def onlineActualT2
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ k : Fin K, (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ c₁ c₂).2.1
end StatisticalRL.OnlineRL

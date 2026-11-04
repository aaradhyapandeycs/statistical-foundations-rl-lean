import Formalization.Online.Regret.W1.W1Definitions

/-! Definition for the actual-path W₃ term. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance W123DefinitionsStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance W123DefinitionsActionDecidable : DecidableEq Action := Classical.decEq Action
noncomputable def onlineActualW3Point
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
  (onlineObservedPlanningRow stage sa.1 sa.2).expectation (fun s => (U s)^2) -
    ((E h).transition sa.1 sa.2).expectation (fun s => (U s)^2)

end StatisticalRL.OnlineRL

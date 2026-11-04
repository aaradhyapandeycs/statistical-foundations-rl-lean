import Formalization.Online.Regret.Joint.W123Definitions
import Formalization.Online.Regret.W2.OnlineW2ActualEpisodeAlignment
import Formalization.Online.Regret.W3.OnlineW3FixedSquareEvent
import Formalization.Online.Regret.W3.OnlineW3AdaptiveSquare

/-! Actual path W₃ split into fixed-optimal square and adaptive square gap. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w3ActualStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w3ActualActionDecidable : DecidableEq Action := Classical.decEq Action

noncomputable def onlineActualW3FixedPoint
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let V := onlineTrueSuffixRowFamily E (h, sa)
  (onlineObservedPlanningRow stage sa.1 sa.2).expectation (fun s => (V s)^2) -
    ((E h).transition sa.1 sa.2).expectation (fun s => (V s)^2)

noncomputable def onlineActualW3AdaptivePoint
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
  let V := onlineTrueSuffixRowFamily E (h, sa)
  (onlineObservedPlanningRow stage sa.1 sa.2).expectation (fun s => (U s)^2 - (V s)^2) -
    ((E h).transition sa.1 sa.2).expectation (fun s => (U s)^2 - (V s)^2)

theorem onlineActualW3Point_eq_fixed_add_adaptive
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) :
    onlineActualW3Point H K hH E initial fallback path δ c₁ c₂ h k =
      onlineActualW3FixedPoint H K hH E initial fallback path δ c₁ c₂ h k +
      onlineActualW3AdaptivePoint H K hH E initial fallback path δ c₁ c₂ h k := by
  simp only [onlineActualW3Point, onlineActualW3FixedPoint, onlineActualW3AdaptivePoint,
    FiniteDistribution.expectation_sub]
  ring
end StatisticalRL.OnlineRL

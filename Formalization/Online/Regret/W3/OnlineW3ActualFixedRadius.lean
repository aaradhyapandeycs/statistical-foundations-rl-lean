import Formalization.Online.Regret.W3.OnlineW3FixedPoint
import Formalization.Online.Regret.W3.OnlineW3SquareVariance
import Formalization.Online.Regret.W1.OnlineW1ActualRadiusAlignment

/-! Actual fixed-optimal squared-value W₃ point, consuming its own simultaneous
fixed-prefix event. The event is an explicit intermediate premise. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w3FixedRadiusStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w3FixedRadiusActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineActualW3FixedPoint_le_radius
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ)
    (hcert : onlineObservedW3SquareCertificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path))
    (h : Fin H) (k : Fin K) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let n := onlineActualW1Count H K hH E initial fallback path δ c₁ c₂ h k
    let V := onlineTrueSuffixRowFamily E (h, sa)
    onlineActualW3FixedPoint H K hH E initial fallback path δ c₁ c₂ h k ≤
      if 3 ≤ n then onlineTrueW1Radius ((H : ℝ)^2) δ n ((E h).transition sa.1 sa.2)
        (fun s => (V s)^2) else (H : ℝ)^2 := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  have hp := onlineObservedW3_fixed_pointwise_bound H K E history k h sa.1 sa.2 δ hcert
  simpa only [onlineActualW3FixedPoint, onlineActualW1Count, onlineW3SquaredTrueFamily,
    planner, history, sa] using hp
end StatisticalRL.OnlineRL

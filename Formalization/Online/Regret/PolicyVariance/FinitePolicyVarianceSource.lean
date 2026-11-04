import Formalization.Online.Regret.PolicyVariance.FiniteTrajectoryVarianceHorizon
import Formalization.MDP.FiniteTrajectory
import Formalization.MDP.FiniteOptimal

/-! Source specialization of the fixed-policy cumulative variance lemma.
Source: onlineRL.tex 648–658, lem:cum-var-ub-Hsquare-ucbvi-mean. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The source deterministic, stage-dependent policy is executed in the
true environment. The expectation is taken under its actual trajectory law. -/
theorem finitePolicy_expected_cumulative_variance_le_horizon_sq
    (H : ℕ) (E : Fin H → EnvironmentStage State Action)
    (π : Fin H → State → Action) (s : State) :
    let D := List.ofFn (fun h => (E h).withPolicy
      (fun t => EnvironmentStage.pointMass (π h t)))
    (DecisionStage.trajectoryLaw D s).expectation (finiteTrajectoryVarianceSum D s) ≤
      (H : ℝ)^2 := by
  dsimp
  simpa only [List.length_ofFn] using
    finiteTrajectory_expected_variance_le_horizon_sq
      (List.ofFn (fun h => (E h).withPolicy (fun t => EnvironmentStage.pointMass (π h t)))) s

end StatisticalRL.OnlineRL

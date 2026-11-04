import Formalization.Online.Regret.PolicyVariance.FiniteTrajectoryVarianceHorizon

/-! Actual-law variance and gap proof component: OnlineEpisodeVariancePotential.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def finiteTrajectoryVariancePotential
    (stages : List (DecisionStage State Action)) (s : State) : ℝ :=
  (DecisionStage.trajectoryLaw stages s).expectation (finiteTrajectoryVarianceSum stages s)

theorem finiteTrajectoryVariancePotential_nil (s : State) :
    finiteTrajectoryVariancePotential ([] : List (DecisionStage State Action)) s = 0 := by
  simp [finiteTrajectoryVariancePotential, finiteTrajectoryVarianceSum]

theorem finiteTrajectoryVariancePotential_cons
    (stage : DecisionStage State Action) (tail : List (DecisionStage State Action)) (s : State) :
    finiteTrajectoryVariancePotential (stage :: tail) s =
      (stage.policy s).expectation (fun a =>
        (stage.transition s a).variance (DecisionStage.trajectoryValue tail) +
        (stage.transition s a).expectation (finiteTrajectoryVariancePotential tail)) := by
  unfold finiteTrajectoryVariancePotential
  rw [DecisionStage.trajectoryExpectation_cons]
  change (stage.policy s).expectation (fun a =>
    (stage.transition s a).expectation (fun t =>
      (DecisionStage.trajectoryLaw tail t).expectation (fun path =>
        (stage.transition s a).variance (DecisionStage.trajectoryValue tail) +
          finiteTrajectoryVarianceSum tail t path))) = _
  simp only [FiniteDistribution.expectation_add, FiniteDistribution.expectation_const]

theorem finiteTrajectoryVariancePotential_range
    (stages : List (DecisionStage State Action)) (s : State) :
    0 ≤ finiteTrajectoryVariancePotential stages s ∧
      finiteTrajectoryVariancePotential stages s ≤ (stages.length : ℝ)^2 := by
  constructor
  · unfold finiteTrajectoryVariancePotential
    apply FiniteDistribution.expectation_nonneg
    intro path
    induction stages generalizing s with
    | nil => simp [finiteTrajectoryVarianceSum]
    | cons stage tail ih =>
      rcases path with ⟨a, t, rest⟩
      exact add_nonneg (FiniteDistribution.variance_nonneg _ _) (ih t rest)
  · exact finiteTrajectory_expected_variance_le_horizon_sq stages s
end StatisticalRL.OnlineRL

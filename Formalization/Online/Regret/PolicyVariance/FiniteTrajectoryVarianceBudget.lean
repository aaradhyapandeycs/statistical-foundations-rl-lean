import Formalization.Online.Regret.PolicyVariance.FiniteTrajectoryVariance

/-! Expected cumulative true transition variance on the actual finite trajectory
is bounded by the variance of its total return. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem finiteTrajectory_expected_variance_le_return_variance
    (stages : List (DecisionStage State Action)) (s : State) :
    (DecisionStage.trajectoryLaw stages s).expectation (finiteTrajectoryVarianceSum stages s) ≤
      (DecisionStage.trajectoryLaw stages s).variance (DecisionStage.pathReward stages s) := by
  induction stages generalizing s with
  | nil =>
      simp [finiteTrajectoryVarianceSum, DecisionStage.pathReward, FiniteDistribution.variance_const]
  | cons stage tail ih =>
      rw [DecisionStage.trajectoryExpectation_cons, finiteTrajectory_return_variance_cons]
      change (stage.policy s).expectation (fun a =>
        (stage.transition s a).expectation (fun t =>
          (DecisionStage.trajectoryLaw tail t).expectation (fun path =>
            (stage.transition s a).variance (DecisionStage.trajectoryValue tail) +
              finiteTrajectoryVarianceSum tail t path))) ≤ _
      simp only [FiniteDistribution.expectation_add, FiniteDistribution.expectation_const]
      have hm : (stage.policy s).expectation (fun a =>
          (stage.transition s a).variance (DecisionStage.trajectoryValue tail) +
          (stage.transition s a).expectation (fun t =>
            (DecisionStage.trajectoryLaw tail t).expectation (finiteTrajectoryVarianceSum tail t))) ≤
          (stage.policy s).expectation (fun a =>
          (stage.transition s a).variance (DecisionStage.trajectoryValue tail) +
          (stage.transition s a).expectation (fun t =>
            (DecisionStage.trajectoryLaw tail t).variance (DecisionStage.pathReward tail t))) := by
        apply FiniteDistribution.expectation_mono
        intro a
        apply add_le_add_right
        apply FiniteDistribution.expectation_mono
        intro t
        exact ih t
      simp only [FiniteDistribution.expectation_add] at hm
      have hnon := (stage.policy s).variance_nonneg (fun a => stage.reward s a +
        (stage.transition s a).expectation (DecisionStage.trajectoryValue tail))
      linarith
end StatisticalRL.OnlineRL

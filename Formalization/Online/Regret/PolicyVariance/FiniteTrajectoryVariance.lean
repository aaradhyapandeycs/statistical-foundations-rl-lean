import Formalization.Probability.FiniteTotalVariance
import Formalization.MDP.FiniteTrajectory
import Formalization.Online.Regret.PolicyVariance.TrajectoryVarianceDefinitions

/-! Variance decomposition and cumulative transition variance for the actual
finite controlled-trajectory law. No adaptive episode-law statement is made. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- One-step total return variance separates action variation, the true-row
variance of the tail value, and the expected remaining return variance. -/
theorem finiteTrajectory_return_variance_cons
    (stage : DecisionStage State Action) (tail : List (DecisionStage State Action)) (s : State) :
    (DecisionStage.trajectoryLaw (stage :: tail) s).variance (DecisionStage.pathReward (stage :: tail) s) =
      (stage.policy s).variance (fun a => stage.reward s a +
        (stage.transition s a).expectation (DecisionStage.trajectoryValue tail)) +
      (stage.policy s).expectation (fun a =>
        (stage.transition s a).variance (DecisionStage.trajectoryValue tail) +
        (stage.transition s a).expectation (fun t =>
          (DecisionStage.trajectoryLaw tail t).variance (DecisionStage.pathReward tail t))) := by
  have hsecond (a : Action) :
      (stage.transition s a).expectation (fun t =>
        (DecisionStage.trajectoryLaw tail t).expectation (fun path =>
          (stage.reward s a + DecisionStage.pathReward tail t path)^2)) =
      (stage.reward s a + (stage.transition s a).expectation (DecisionStage.trajectoryValue tail))^2 +
      (stage.transition s a).variance (DecisionStage.trajectoryValue tail) +
      (stage.transition s a).expectation (fun t =>
        (DecisionStage.trajectoryLaw tail t).variance (DecisionStage.pathReward tail t)) := by
    have hinner (t : State) :
        (DecisionStage.trajectoryLaw tail t).expectation (fun path =>
          (stage.reward s a + DecisionStage.pathReward tail t path)^2) =
        (stage.reward s a)^2 + 2 * stage.reward s a * DecisionStage.trajectoryValue tail t +
          (DecisionStage.trajectoryLaw tail t).expectation (fun path => (DecisionStage.pathReward tail t path)^2) := by
      have he : (fun path => (stage.reward s a + DecisionStage.pathReward tail t path)^2) =
          (fun path => (stage.reward s a)^2 + (2 * stage.reward s a) * DecisionStage.pathReward tail t path +
            (DecisionStage.pathReward tail t path)^2) := by funext path; ring
      rw [he, FiniteDistribution.expectation_add, FiniteDistribution.expectation_add,
        FiniteDistribution.expectation_const, FiniteDistribution.expectation_mul]
      rfl
    simp_rw [hinner]
    simp only [FiniteDistribution.expectation_add, FiniteDistribution.expectation_const,
      FiniteDistribution.expectation_mul, FiniteDistribution.variance,
      FiniteDistribution.expectation_sub]
    have heq : (fun x => ((DecisionStage.trajectoryLaw tail x).expectation (DecisionStage.pathReward tail x))^2) =
        (fun x => (DecisionStage.trajectoryValue tail x)^2) := rfl
    rw [heq]
    ring
  unfold FiniteDistribution.variance
  rw [DecisionStage.trajectoryExpectation_cons, DecisionStage.trajectoryExpectation_cons]
  change (stage.policy s).expectation (fun a =>
      (stage.transition s a).expectation (fun t =>
        (DecisionStage.trajectoryLaw tail t).expectation (fun path =>
          (stage.reward s a + DecisionStage.pathReward tail t path)^2))) - _ = _
  simp_rw [hsecond]
  simp only [DecisionStage.pathReward, FiniteDistribution.expectation_add,
    FiniteDistribution.expectation_const, FiniteDistribution.variance]
  have heq : (fun x => (DecisionStage.trajectoryLaw tail x).expectation (DecisionStage.pathReward tail x)) =
      DecisionStage.trajectoryValue tail := rfl
  rw [heq]
  ring
end StatisticalRL.OnlineRL

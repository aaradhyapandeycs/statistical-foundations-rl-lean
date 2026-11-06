import Formalization.MDP.TrajectoryDefinitions
open scoped BigOperators
namespace StatisticalRL.DecisionStage
variable {State Action : Type*} [Fintype State] [Fintype Action]
/-- The trajectory law with the first state/action supplied rather than sampled.
Its carrier stores the next state and every remaining action/state pair. -/
def actionTrajectoryLaw (stage : DecisionStage State Action)
    (tail : List (DecisionStage State Action)) (s : State) (a : Action) :
    FiniteDistribution (State × FinitePath State Action tail.length) where
  prob path := (stage.transition s a).prob path.1 * pathWeight tail path.1 path.2
  prob_nonneg path :=
    mul_nonneg ((stage.transition s a).prob_nonneg _) ((trajectoryLaw tail path.1).prob_nonneg path.2)
  sum_prob := by
    have sum_pathWeight (t : State) : ∑ path, pathWeight tail t path = 1 :=
      (trajectoryLaw tail t).sum_prob
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, sum_pathWeight, mul_one]
    exact (stage.transition s a).sum_prob

/-- Actual cumulative-reward expectation with its initial action held fixed.
The empty-stage case is the source's terminal `Q = 0` convention. -/
def trajectoryQ : List (DecisionStage State Action) → State → Action → ℝ
  | [] => fun _ _ ↦ 0
  | stage :: tail => fun s a ↦
    (actionTrajectoryLaw stage tail s a).expectation (fun path ↦
      stage.reward s a + pathReward tail path.1 path.2)


end StatisticalRL.DecisionStage

import Formalization.MDP.DecisionStageDefinitions
import Formalization.Online.SourceOptimism.FinitePathHistoryDefinitions
open scoped BigOperators
namespace StatisticalRL.DecisionStage
variable {State Action : Type*} [Fintype State] [Fintype Action]
/-- The joint mass of an actual action/state trajectory from the given state.
In particular, tail policies are evaluated at the sampled next state. -/
def pathWeight : (stages : List (DecisionStage State Action)) → State →
    FinitePath State Action stages.length → ℝ
  | [], _, _ => 1
  | stage :: tail, s, path =>
    (stage.policy s).prob path.1 * (stage.transition s path.1).prob path.2.1 *
      pathWeight tail path.2.1 path.2.2

/-- The actual undiscounted sum of stage rewards along a finite trajectory. -/
def pathReward : (stages : List (DecisionStage State Action)) → State →
    FinitePath State Action stages.length → ℝ
  | [], _, _ => 0
  | stage :: tail, s, path =>
    stage.reward s path.1 + pathReward tail path.2.1 path.2.2

/-- A normalized finite probability law on actual trajectories of the episode. -/
def trajectoryLaw (stages : List (DecisionStage State Action)) (s : State) :
    FiniteDistribution (FinitePath State Action stages.length) where
  prob := pathWeight stages s
  prob_nonneg := by
    intro path
    induction stages generalizing s with
      | nil => exact zero_le_one
      | cons stage tail ih =>
        exact mul_nonneg
          (mul_nonneg ((stage.policy s).prob_nonneg _) ((stage.transition s path.1).prob_nonneg _))
          (ih _ _)
  sum_prob := by
    induction stages generalizing s with
      | nil => simp [pathWeight, FinitePath]
      | cons stage tail ih =>
        change (∑ path : Action × State × FinitePath State Action tail.length,
          (stage.policy s).prob path.1 * (stage.transition s path.1).prob path.2.1 *
            pathWeight tail path.2.1 path.2.2) = 1
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, ih, mul_one]
        simp only [← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]

/-- Expected cumulative reward under the separately constructed trajectory law. -/
def trajectoryValue (stages : List (DecisionStage State Action)) (s : State) : ℝ :=
  (trajectoryLaw stages s).expectation (pathReward stages s)


end StatisticalRL.DecisionStage

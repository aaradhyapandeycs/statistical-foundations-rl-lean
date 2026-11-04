import Formalization.Probability.Variance
import Formalization.MDP.FiniteTrajectory

/-! Cumulative true transition variance along a controlled finite path. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Sum of true transition variances along an actual controlled finite path. -/
noncomputable def finiteTrajectoryVarianceSum :
    (stages : List (DecisionStage State Action)) → State →
      FinitePath State Action stages.length → ℝ
  | [], _, _ => 0
  | stage :: tail, s, path =>
      (stage.transition s path.1).variance (DecisionStage.trajectoryValue tail) +
        finiteTrajectoryVarianceSum tail path.2.1 path.2.2

end StatisticalRL.OnlineRL

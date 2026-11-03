import Formalization.MDP.OptimalTrajectoryValue

/-! Two-common-policy comparison transferred to actual own-model optimal trajectory Q. -/
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Compare each model under the two actual optimal greedy policies, then use
own-model optimality. The policies need not be optimal in the other model. -/
theorem qStopped_optimal_transfer_of_two_policy_bounds
    (M M' : DiscountedMDP State Action) (C : ℝ)
    (hleft : ∀ s a,
      |M'.trajectoryExpectedQ M'.optimalGreedyPolicy s a -
        M.trajectoryExpectedQ M'.optimalGreedyPolicy s a| ≤ C)
    (hright : ∀ s a,
      |M'.trajectoryExpectedQ M.optimalGreedyPolicy s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ C)
    (s : State) (a : Action) :
    |M'.trajectoryExpectedQ M'.optimalGreedyPolicy s a -
      M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ C := by
  apply abs_le.mpr
  constructor
  · have hp := (abs_le.mp (hright s a)).1
    have ho := M'.trajectoryQ_le_optimalGreedy M.optimalGreedyPolicy s a
    linarith
  · have hp := (abs_le.mp (hleft s a)).2
    have ho := M.trajectoryQ_le_optimalGreedy M'.optimalGreedyPolicy s a
    linarith

end StatisticalRL.QLearning

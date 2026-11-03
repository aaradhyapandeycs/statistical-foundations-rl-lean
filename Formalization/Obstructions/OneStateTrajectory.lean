import Formalization.Obstructions.OneState
import Formalization.MDP.OptimalTrajectoryValue

/-! Exact known-reward one-state Q estimator for actual infinite trajectories. -/

open MeasureTheory

namespace StatisticalRL.Obstructions

variable {State Action Data : Type*} [Fintype State] [Fintype Action] [Nonempty Action]

/-- The fixed estimator reads only the known reward and discount and ignores all data. -/
noncomputable def oneStateKnownRewardEstimator (reward : State → Action → ℝ)
    (discount : ℝ) (_ : Data) : State → Action → ℝ :=
  fun s a ↦ reward s a + discount * actionMaximum (reward s) / (1 - discount)

omit [Nonempty Action] in
/-- The actual optimal greedy policy's forced-action infinite return is the known formula. -/
theorem oneState_trajectoryOptimalQ [Subsingleton State] (M : DiscountedMDP State Action)
    (s : State) (a : Action) :
    M.trajectoryExpectedQ M.optimalGreedyPolicy s a = oneStateQ M s a := by
  rw [M.optimalGreedy_trajectoryQ, optimalityFixedPoint_eq_oneStateQ]

omit [Nonempty Action] in
/-- The formula dominates actual forced-action Q for every stationary randomized policy. -/
theorem oneState_trajectoryQ_le [Subsingleton State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    M.trajectoryExpectedQ π s a ≤ oneStateQ M s a := by
  rw [← oneState_trajectoryOptimalQ M]
  exact M.trajectoryQ_le_optimalGreedy π s a

omit [Nonempty Action] in
/-- The known reward maximizing policy itself attains the actual trajectory optimum. -/
theorem oneState_rewardGreedy_trajectoryQ [Subsingleton State] (M : DiscountedMDP State Action)
    (s : State) (a : Action) :
    M.trajectoryExpectedQ (oneStateGreedyPolicy M) s a = oneStateQ M s a := by
  rw [M.trajectoryExpectedQ_eq_policyFixedPoint, greedy_policyFixedPoint_eq_optimalityFixedPoint,
    optimalityFixedPoint_eq_oneStateQ]

/-- One estimator works for all admissible transitions and every possible data value. -/
theorem oneStateKnownRewardEstimator_exact [Subsingleton State]
    (reward : State → Action → ℝ) (discount : ℝ) (M : DiscountedMDP State Action)
    (hr : M.reward = reward) (hγ : M.discount = discount) (data : Data) :
    oneStateKnownRewardEstimator reward discount data =
      fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a := by
  funext s a
  rw [oneState_trajectoryOptimalQ]
  simp only [oneStateKnownRewardEstimator, oneStateQ, hr, hγ]

/-- Error is zero on every data value, uniformly in the transition kernel. -/
theorem oneStateKnownRewardEstimator_norm_error [Subsingleton State]
    (reward : State → Action → ℝ) (discount : ℝ) (M : DiscountedMDP State Action)
    (hr : M.reward = reward) (hγ : M.discount = discount) (data : Data) :
    ‖oneStateKnownRewardEstimator reward discount data -
      (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖ = 0 := by
  rw [oneStateKnownRewardEstimator_exact reward discount M hr hγ data, sub_self, norm_zero]

/-- The strict-error event has zero mass under every data law. -/
theorem oneStateKnownRewardEstimator_error_measure [Subsingleton State] [MeasurableSpace Data]
    (μ : Measure Data) (reward : State → Action → ℝ) (discount : ℝ)
    (M : DiscountedMDP State Action) (hr : M.reward = reward) (hγ : M.discount = discount)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ {data | ε < ‖oneStateKnownRewardEstimator reward discount data -
      (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖} = 0 := by
  have hempty : {data : Data | ε < ‖oneStateKnownRewardEstimator reward discount data -
      (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖} = ∅ := by
    ext data
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rw [oneStateKnownRewardEstimator_norm_error reward discount M hr hγ data]
    exact not_lt_of_ge hε
  rw [hempty, measure_empty]

end StatisticalRL.Obstructions

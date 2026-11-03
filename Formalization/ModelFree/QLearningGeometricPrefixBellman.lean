import Formalization.ModelFree.QLearningGeometricPrefixReward

/-! Finite forced-prefix discounted sums, policy Bellman iterates, and actual trajectory Q. -/
namespace StatisticalRL.QLearning
open Filter Topology
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Finite expectation commutes with a finite time sum. -/
theorem qPrefix_expectation_finset_sum {Ω : Type*} [Fintype Ω]
    (d : FiniteDistribution Ω) (n : ℕ) (f : ℕ → Ω → ℝ) :
    d.expectation (fun x => ∑ k ∈ Finset.range n, f k x) =
      ∑ k ∈ Finset.range n, d.expectation (f k) := by
  classical
  simp only [FiniteDistribution.expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- n+1 rewards consist of the forced initial reward and n subsequent rewards.
The next state and next policy action are integrated exactly once. -/
theorem qPrefixDiscountedSum_succ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) :
    qPrefixDiscountedSum M π (n + 1) = M.qBellman π (qPrefixDiscountedSum M π n) := by
  classical
  funext s a
  unfold qPrefixDiscountedSum
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, qPrefixRewardMean_zero]
  unfold DiscountedMDP.qBellman
  rw [add_comm]
  congr 1
  simp_rw [qPrefixRewardMean_succ, pow_succ]
  simp_rw [qPrefix_expectation_finset_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [FiniteDistribution.expectation_mul]
  ring

/-- No normalization factor or extra final transition appears in the finite
identity. It holds at discount zero without a case split. -/
theorem qPrefixDiscountedSum_eq_iterate (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (n : ℕ) :
    qPrefixDiscountedSum M π n = (M.qBellman π)^[n] 0 := by
  induction n with
  | zero =>
      funext s a
      simp [qPrefixDiscountedSum]
  | succ n ih =>
      rw [qPrefixDiscountedSum_succ, Function.iterate_succ_apply', ih]

/-- Actual finite-prefix discounted reward converges to actual forced-action
trajectory Q for every initial action, including a zero-policy-support action. -/
theorem qPrefixDiscountedSum_tendsto_trajectoryQ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    Tendsto (fun n => qPrefixDiscountedSum M π n s a) atTop
      (𝓝 (M.trajectoryExpectedQ π s a)) := by
  simp_rw [qPrefixDiscountedSum_eq_iterate]
  rw [M.trajectoryExpectedQ_eq_policyFixedPoint]
  exact (tendsto_pi_nhds.mp
    ((tendsto_pi_nhds.mp (M.tendsto_policy_evaluation_iteration π 0)) s)) a

/-- A HasSum formulation supplies summability and the Q identification together,
without introducing a separate assumed convergence estimate. -/
theorem qPrefixRewardMean_hasSum_trajectoryQ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    HasSum (fun k => M.discount ^ k * qPrefixRewardMean M π k s a)
      (M.trajectoryExpectedQ π s a) := by
  have hs : Summable (fun k => ‖M.discount ^ k * qPrefixRewardMean M π k s a‖) := by
    apply Summable.of_nonneg_of_le
      (fun k => norm_nonneg _) _
      (summable_geometric_of_lt_one M.discount_nonneg M.discount_lt_one)
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (pow_nonneg M.discount_nonneg k) (qPrefixRewardMean_bounds M π k s a).1)]
    exact mul_le_of_le_one_right (pow_nonneg M.discount_nonneg k)
      (qPrefixRewardMean_bounds M π k s a).2
  exact (hasSum_iff_tendsto_nat_of_summable_norm hs).2
    (qPrefixDiscountedSum_tendsto_trajectoryQ M π s a)

/-- Discounted terminal-reward series equals actual trajectory Q. -/
theorem qPrefixRewardMean_tsum_eq_trajectoryQ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    (∑' k, M.discount ^ k * qPrefixRewardMean M π k s a) =
      M.trajectoryExpectedQ π s a :=
  (qPrefixRewardMean_hasSum_trajectoryQ M π s a).tsum_eq

end StatisticalRL.QLearning

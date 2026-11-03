import Formalization.ModelFree.QLearningStoppedPrefixRewardMeasure
import Formalization.ModelFree.QLearningStoppedPrefixPayoffTV
import Formalization.ModelFree.QLearningStoppedPrefixOptimalTransfer

/-! Conditional fixed-policy and optimal-Q stability from explicit stopped-law information bounds. -/
namespace StatisticalRL.QLearning
open scoped BigOperators
open CountablePinsker
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Same known rewards give one common payoff on each actual stopped prefix. -/
theorem qStopped_same_reward_payoff (M M' : DiscountedMDP State Action)
    (hr : M'.reward = M.reward) (s : State) (a : Action)
    (z : qStoppedPrefixAbsCarrier (State := State) (Action := Action)) :
    qRewardStopped_payoff M' s a z = qRewardStopped_payoff M s a z := by
  rcases z with ⟨k, path⟩
  change qPrefixTerminalReward M' s a k path = qPrefixTerminalReward M s a k path
  induction k generalizing s a with
  | zero => exact congrFun (congrFun hr s) a
  | succ k ih => exact ih path.1 path.2.1 path.2.2

/-- The positive horizon gap is the sole divided quantity. Zero rho/gamma
requires no exceptional cancellation or positive-radius assumption. -/
theorem qStopped_sqrt_radius_identity (ρ γ h : ℝ) (hh : 0 < h) :
    Real.sqrt ((ρ * γ / h) / 2) / h = Real.sqrt (ρ * γ / (2 * h ^ 3)) := by
  calc
    Real.sqrt ((ρ * γ / h) / 2) / h =
        Real.sqrt (((ρ * γ / h) / 2) / h ^ 2) := by
      rw [Real.sqrt_div' _ (sq_nonneg h), Real.sqrt_sq (le_of_lt hh)]
    _ = Real.sqrt (ρ * γ / (2 * h ^ 3)) := by
      congr 1
      field_simp [ne_of_gt hh]
      <;> ring

/-- Fixed common policy assembly. K is the stopped KL upper-bound quantity;
Pinsker and the actual KL estimate are supplied independently and visibly. -/
theorem qStopped_fixed_policy_stability_of_pinsker_kl
    (M M' : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (hr : M'.reward = M.reward) (hγ : M'.discount = M.discount)
    (ρ K : ℝ) (s : State) (a : Action)
    (hPinsker : (1 / 2 : ℝ) * ∑' z : qStoppedPrefixAbsCarrier
        (State := State) (Action := Action),
        |qActualStoppedPrefixMass M' π M.discount s a z -
          qActualStoppedPrefixMass M π M.discount s a z| ≤ Real.sqrt (K / 2))
    (hKL : K ≤ ρ * M.discount / (1 - M.discount)) :
    |M'.trajectoryExpectedQ π s a - M.trajectoryExpectedQ π s a| ≤
      Real.sqrt (ρ * M.discount / (2 * (1 - M.discount) ^ 3)) := by
  let p := qActualStoppedPrefixMass M π M.discount s a
  let q := qActualStoppedPrefixMass M' π M.discount s a
  let R := qRewardStopped_payoff M s a
  have hn (N : DiscountedMDP State Action) :
      ∀ z : qStoppedPrefixAbsCarrier (State := State) (Action := Action),
        0 ≤ qActualStoppedPrefixMass N π M.discount s a z := by
    rintro ⟨k, path⟩
    exact mul_nonneg (qGeometricStopWeight_nonneg M.discount k
      M.discount_nonneg M.discount_lt_one) ((qForcedPrefixLaw N π s a k).prob_nonneg path)
  have hb : ∀ z, 0 ≤ R z ∧ R z ≤ 1 := by
    rintro ⟨k, path⟩
    exact qPrefixTerminalReward_bounds M s a k path
  have hpay := qStopped_bounded_payoff_of_halfL1_bound p q R
    (hn M) (hn M')
    (qRewardStopped_mass_hasSum M π M.discount s a M.discount_nonneg M.discount_lt_one)
    (qRewardStopped_mass_hasSum M' π M.discount s a M.discount_nonneg M.discount_lt_one)
    hb (Real.sqrt (K / 2)) hPinsker
  have hprime : (∑' z, q z * R z) =
      (1 - M.discount) * M'.trajectoryExpectedQ π s a := by
    change (∑' z, qActualStoppedPrefixMass M' π M.discount s a z *
      qRewardStopped_payoff M s a z) = _
    simp_rw [← qStopped_same_reward_payoff M M' hr s a]
    rw [← hγ, qRewardStopped_payoff_eq_trajectoryQ]
  have hnom : (∑' z, p z * R z) =
      (1 - M.discount) * M.trajectoryExpectedQ π s a :=
    qRewardStopped_payoff_eq_trajectoryQ M π s a
  rw [hprime, hnom, ← mul_sub, abs_mul,
    abs_of_pos (sub_pos.mpr M.discount_lt_one)] at hpay
  have hgap := sub_pos.mpr M.discount_lt_one
  have hdiv : |M'.trajectoryExpectedQ π s a - M.trajectoryExpectedQ π s a| ≤
      Real.sqrt (K / 2) / (1 - M.discount) :=
    (le_div_iff₀ hgap).2 (by simpa only [mul_comm] using hpay)
  calc
    _ ≤ Real.sqrt (K / 2) / (1 - M.discount) := hdiv
    _ ≤ Real.sqrt ((ρ * M.discount / (1 - M.discount)) / 2) /
        (1 - M.discount) := div_le_div_of_nonneg_right
          (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hKL (by norm_num)))
          (le_of_lt hgap)
    _ = _ := qStopped_sqrt_radius_identity ρ M.discount (1 - M.discount) hgap

/-- Only the two own-model greedy policies are needed from the uniform
countable-law inputs; no maximizer over an unbounded policy space is introduced. -/
theorem qStopped_optimal_stability_of_pinsker_kl
    (M M' : DiscountedMDP State Action)
    (hr : M'.reward = M.reward) (hγ : M'.discount = M.discount)
    (ρ : ℝ) (K : StationaryPolicy State Action → State → Action → ℝ)
    (hPinsker : ∀ π s a, (1 / 2 : ℝ) * ∑' z : qStoppedPrefixAbsCarrier
        (State := State) (Action := Action),
        |qActualStoppedPrefixMass M' π M.discount s a z -
          qActualStoppedPrefixMass M π M.discount s a z| ≤ Real.sqrt (K π s a / 2))
    (hKL : ∀ π s a, K π s a ≤ ρ * M.discount / (1 - M.discount))
    (s : State) (a : Action) :
    |M'.trajectoryExpectedQ M'.optimalGreedyPolicy s a -
      M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
      Real.sqrt (ρ * M.discount / (2 * (1 - M.discount) ^ 3)) := by
  apply qStopped_optimal_transfer_of_two_policy_bounds M M'
  · intro x b
    exact qStopped_fixed_policy_stability_of_pinsker_kl M M' M'.optimalGreedyPolicy
      hr hγ ρ (K M'.optimalGreedyPolicy x b) x b
      (hPinsker _ _ _) (hKL _ _ _)
  · intro x b
    exact qStopped_fixed_policy_stability_of_pinsker_kl M M' M.optimalGreedyPolicy
      hr hγ ρ (K M.optimalGreedyPolicy x b) x b
      (hPinsker _ _ _) (hKL _ _ _)

end StatisticalRL.QLearning

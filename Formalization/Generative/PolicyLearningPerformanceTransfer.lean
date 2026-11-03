import Formalization.Generative.PolicyLearningHoeffding

/-! Deterministic performance transfer for actual trajectory values. -/
namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Forced-first-action values use the same actual continuation trajectory value,
including actions outside the support of the policy. -/
theorem trajectoryQ_eq_reward_add_trajectoryValue (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    M.trajectoryExpectedQ π s a = M.reward s a + M.discount *
      (M.transition s a).expectation (M.trajectoryExpectedValue π) := by
  rw [M.trajectoryExpectedQ_eq_policyFixedPoint,
    M.policyFixedPoint_eq_reward_add_value, M.trajectoryExpectedValue_eq_valueFixedPoint]

/-- The exact source Q-loss identity contains a factor of the discount. -/
theorem trajectoryQ_sub_eq_discount_expectation_value_sub
    (M : DiscountedMDP State Action) (π τ : StationaryPolicy State Action)
    (s : State) (a : Action) :
    M.trajectoryExpectedQ π s a - M.trajectoryExpectedQ τ s a =
      M.discount * (M.transition s a).expectation
        (M.trajectoryExpectedValue π - M.trajectoryExpectedValue τ) := by
  rw [M.trajectoryQ_eq_reward_add_trajectoryValue,
    M.trajectoryQ_eq_reward_add_trajectoryValue]
  change _ = M.discount * (M.transition s a).expectation
    (fun t ↦ M.trajectoryExpectedValue π t - M.trajectoryExpectedValue τ t)
  rw [FiniteDistribution.expectation_sub]
  ring

/-- A uniform true-model V-loss bound implies the source Q bound without
any positive-discount assumption. -/
theorem trajectoryQ_loss_le_discount_of_value_loss
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ε : ℝ) (hV : ∀ s, M.trajectoryExpectedValue M.optimalGreedyPolicy s -
      M.trajectoryExpectedValue π s ≤ ε) (s : State) (a : Action) :
    0 ≤ M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
      M.trajectoryExpectedQ π s a ∧
    M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
      M.trajectoryExpectedQ π s a ≤ M.discount * ε := by
  refine ⟨sub_nonneg.mpr (M.trajectoryQ_le_optimalGreedy π s a), ?_⟩
  rw [M.trajectoryQ_sub_eq_discount_expectation_value_sub]
  exact mul_le_mul_of_nonneg_left
    ((M.transition s a).expectation_le_const hV) M.discount_nonneg

/-- Supremum-norm form of the V-to-Q implication, with the exact discount
factor and actual optimal-policy domination supplying the absolute values. -/
theorem trajectoryQ_loss_norm_le_discount_of_value_loss
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hV : ∀ s, M.trajectoryExpectedValue M.optimalGreedyPolicy s -
      M.trajectoryExpectedValue π s ≤ ε) :
    ‖M.trajectoryExpectedValue M.optimalGreedyPolicy - M.trajectoryExpectedValue π‖ ≤ ε ∧
    ‖M.trajectoryExpectedQ M.optimalGreedyPolicy - M.trajectoryExpectedQ π‖ ≤
      M.discount * ε := by
  constructor
  · apply (pi_norm_le_iff_of_nonneg hε).2
    intro s
    simpa only [Pi.sub_apply, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (M.trajectoryValue_le_optimalGreedy π s))] using hV s
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg M.discount_nonneg hε)).2
    intro s
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg M.discount_nonneg hε)).2
    intro a
    have h := M.trajectoryQ_loss_le_discount_of_value_loss π ε hV s a
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

end StatisticalRL.DiscountedMDP

namespace StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Actual empirical optimality, rather than an assumed performance bound,
yields both source guarantees from the two evaluation-error budgets. The
fitted policy and both empirical values use exactly the same data. -/
theorem policyEstimator_performance_of_evaluation_errors
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (ε₀ ε₁ : ℝ)
    (h₀ : ‖(empiricalModel M N hN data).trajectoryExpectedValue M.optimalGreedyPolicy -
      M.trajectoryExpectedValue M.optimalGreedyPolicy‖ ≤ ε₀)
    (h₁ : ‖(empiricalModel M N hN data).trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) -
      M.trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t))‖ ≤ ε₁) :
    (∀ s, 0 ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s -
        M.trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s ∧
      M.trajectoryExpectedValue M.optimalGreedyPolicy s -
        M.trajectoryExpectedValue
          (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s ≤ ε₀ + ε₁) ∧
    (∀ s a, 0 ≤ M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
        M.trajectoryExpectedQ
          (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s a ∧
      M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
        M.trajectoryExpectedQ
          (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s a ≤
        M.discount * (ε₀ + ε₁)) := by
  have hv (s : State) := (policyEstimator_loss_le_evaluation_errors M N hN data s).trans
    (add_le_add h₀ h₁)
  exact ⟨fun s ↦ ⟨sub_nonneg.mpr (M.trajectoryValue_le_optimalGreedy _ s), hv s⟩,
    fun s a ↦ M.trajectoryQ_loss_le_discount_of_value_loss _ _ hv s a⟩

end StatisticalRL.ModelBasedPolicyLearning

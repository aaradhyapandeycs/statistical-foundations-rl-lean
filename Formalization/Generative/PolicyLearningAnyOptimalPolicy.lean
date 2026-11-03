import Formalization.Generative.PolicyLearningFittedPolicyEvaluation
import Formalization.Generative.PolicyLearningPerformanceTransfer

/-! Uniform source intermediate bounds for all deterministic empirical optima. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyLearning
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

/-- Actual empirical trajectory optimality, against all stationary policies. -/
def EmpiricallyOptimal (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (f : State → Action) : Prop :=
  ∀ π s, (empiricalModel M N hN data).trajectoryExpectedValue π s ≤
    (empiricalModel M N hN data).trajectoryExpectedValue
      (fun t ↦ EnvironmentStage.pointMass (f t)) s

theorem policyEstimator_empiricallyOptimal (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) :
    EmpiricallyOptimal M N hN data (policyEstimator M N hN data) := by
  intro π s
  exact policyEstimator_empirical_optimal M N hN data π s

theorem empiricallyOptimal_value_eq (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) (f : State → Action)
    (hf : EmpiricallyOptimal M N hN data f) :
    (empiricalModel M N hN data).trajectoryExpectedValue
      (fun t ↦ EnvironmentStage.pointMass (f t)) = valueEstimator M N hN data := by
  funext s
  apply le_antisymm
  · exact policyEstimator_empirical_optimal M N hN data _ s
  · exact hf _ s

/-- Deterministic performance comparison for every empirical-optimal tie choice. -/
theorem empiricallyOptimal_performance (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) (f : State → Action)
    (hf : EmpiricallyOptimal M N hN data f) (ε₀ ε₁ : ℝ)
    (h₀ : ‖(empiricalModel M N hN data).trajectoryExpectedValue M.optimalGreedyPolicy -
      M.trajectoryExpectedValue M.optimalGreedyPolicy‖ ≤ ε₀)
    (h₁ : ‖(empiricalModel M N hN data).trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (f t)) -
      M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤ ε₁) :
    (∀ s, 0 ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s -
       M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ∧
       M.trajectoryExpectedValue M.optimalGreedyPolicy s -
       M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s ≤ ε₀ + ε₁) ∧
    (∀ s a, 0 ≤ M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
       M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ∧
       M.trajectoryExpectedQ M.optimalGreedyPolicy s a -
       M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ≤
         M.discount * (ε₀ + ε₁)) := by
  let H := empiricalModel M N hN data
  let π := fun t ↦ EnvironmentStage.pointMass (f t)
  have hv (s : State) : M.trajectoryExpectedValue M.optimalGreedyPolicy s -
      M.trajectoryExpectedValue π s ≤ ε₀ + ε₁ := by
    have ho := hf M.optimalGreedyPolicy s
    have ha := norm_le_pi_norm (H.trajectoryExpectedValue M.optimalGreedyPolicy -
      M.trajectoryExpectedValue M.optimalGreedyPolicy) s
    have hb := norm_le_pi_norm (H.trajectoryExpectedValue π - M.trajectoryExpectedValue π) s
    simp only [Pi.sub_apply, Real.norm_eq_abs] at ha hb
    have ha' := neg_abs_le (H.trajectoryExpectedValue M.optimalGreedyPolicy s -
      M.trajectoryExpectedValue M.optimalGreedyPolicy s)
    have hb' := le_abs_self (H.trajectoryExpectedValue π s - M.trajectoryExpectedValue π s)
    change H.trajectoryExpectedValue M.optimalGreedyPolicy s ≤ H.trajectoryExpectedValue π s at ho
    linarith
  exact ⟨fun s ↦ ⟨sub_nonneg.mpr (M.trajectoryValue_le_optimalGreedy _ s), hv s⟩,
    fun s a ↦ M.trajectoryQ_loss_le_discount_of_value_loss _ _ hv s a⟩

/-- A single actual-sampling event controls every empirical-optimal deterministic
policy, including any tie choice selected after seeing the data. -/
theorem all_empiricallyOptimal_evaluation_source_bound
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ / 2 < (samplingLaw M N).real {data |
      ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
      ‖valueEstimator M N hN data - M.trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
      2 * Real.sqrt (2 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 3)) +
        6 * leaveOneOutBeta M N δ / (N * (1 - M.discount) ^ 2)} := by
  let μ := samplingLaw M N
  let β := leaveOneOutBeta M N δ
  have hβ : 0 ≤ β := le_trans (by norm_num) (leaveOneOutBeta_ge_four M N hN δ hδ hδ1)
  let good : Set (Samples State Action N) := {data |
      ∀ (x : State) (a : Action),
      |(empiricalRow N hN data x a).expectation (valueEstimator M N hN data) -
        (M.transition x a).expectation (valueEstimator M N hN data)| ≤
      Real.sqrt (β / N) * Real.sqrt ((M.transition x a).variance (valueEstimator M N hN data)) +
        2 * β / (N * (1 - M.discount))}
  have hs : 1 - δ / 2 < μ.real good := empiricalOptimalValue_allRows_residual M N hN δ hδ hδ1
  let target : Set (Samples State Action N) := {data |
      ∀ f : State → Action, EmpiricallyOptimal M N hN data f →
      ‖valueEstimator M N hN data - M.trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (f t))‖ ≤
      2 * Real.sqrt (2 * β / (N * (1 - M.discount) ^ 3)) +
        6 * β / (N * (1 - M.discount) ^ 2)}
  have hsub : good ⊆ target := by
    intro data hd f hf
    have heq := empiricallyOptimal_value_eq M N hN data f hf
    rw [← heq]
    apply empiricalPolicyValue_source_error_bound M (empiricalModel M N hN data)
      (fun t ↦ EnvironmentStage.pointMass (f t)) rfl rfl N hN β hβ
    intro s
    unfold empiricalPolicyValueResidual
    rw [deterministicPolicyTransition_expectation, deterministicPolicyTransition_expectation]
    unfold FiniteDistribution.variance
    rw [deterministicPolicyTransition_expectation, deterministicPolicyTransition_expectation]
    rw [heq]
    exact hd s (f s)
  exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ target))

end StatisticalRL.ModelBasedPolicyLearning

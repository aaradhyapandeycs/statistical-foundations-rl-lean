import Formalization.Generative.PolicyLearningEmpiricalOptimalResidual
import Formalization.Generative.PolicyLearningVarianceResolventBridge

/-! Actual-law fitted-policy evaluation guarantee from one common event. -/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyLearning
open StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance fittedEvaluationStateMeasurable : MeasurableSpace State := ⊤

/-- A point-mass stationary policy's transition expectation is the selected
state-action row expectation, for any valid MDP and continuation vector. -/
theorem deterministicPolicyTransition_expectation (M : DiscountedMDP State Action)
    (f : State → Action) (s : State) (V : State → ℝ) :
    (M.policyTransition (fun t ↦ EnvironmentStage.pointMass (f t)) s).expectation V =
      (M.transition s (f s)).expectation V := by
  unfold DiscountedMDP.policyTransition
  rw [FiniteDistribution.expectation_bind, EnvironmentStage.expectation_pointMass]

/-- The true policy-row variance at the realized greedy policy equals the
true transition-row variance at its selected action. -/
theorem policyEstimator_truePolicyVariance_eq_row (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) (s : State) :
    (M.policyTransition (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s).variance
        (valueEstimator M N hN data) =
      (M.transition s (policyEstimator M N hN data s)).variance (valueEstimator M N hN data) := by
  unfold FiniteDistribution.variance
  rw [deterministicPolicyTransition_expectation, deterministicPolicyTransition_expectation]

/-- The fitted policy's empirical-minus-true residual equals the source
state-action row residual at its realized greedy action. -/
theorem policyEstimator_policyResidual_eq_row (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) (s : State) :
    empiricalPolicyValueResidual M (empiricalModel M N hN data)
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s =
      (empiricalRow N hN data s (policyEstimator M N hN data s)).expectation (valueEstimator M N hN data) -
        (M.transition s (policyEstimator M N hN data s)).expectation (valueEstimator M N hN data) := by
  unfold empiricalPolicyValueResidual
  rw [deterministicPolicyTransition_expectation, deterministicPolicyTransition_expectation]
  rfl

/-- Source fitted-policy evaluation bound from the actual all-action residual
event, with its precise β and strict probability. The selected policy is
chosen only after the universal event holds. -/
theorem policyEstimator_evaluation_source_bound (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ / 2 < (samplingLaw M N).real {data |
      ‖valueEstimator M N hN data - M.trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t))‖ ≤
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
      ‖valueEstimator M N hN data - M.trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t))‖ ≤
      2 * Real.sqrt (2 * β / (N * (1 - M.discount) ^ 3)) +
        6 * β / (N * (1 - M.discount) ^ 2)}
  have hsub : good ⊆ target := by
    intro data hd
    apply policyEstimator_source_error_bound_conditional M N hN data β hβ
    intro s
    rw [policyEstimator_policyResidual_eq_row, policyEstimator_truePolicyVariance_eq_row]
    exact hd s (policyEstimator M N hN data s)
  exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ target))

end StatisticalRL.ModelBasedPolicyLearning

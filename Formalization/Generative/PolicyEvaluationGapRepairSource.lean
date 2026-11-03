import Formalization.Generative.PolicyEvaluationAllSampleRepair
import Formalization.Generative.PolicyEvaluationBetaSourceCompare

/-! Source-radius composition of the all-positive-sample event and the
manuscript-beta comparison for state spaces of size at least two. The
one-state exactness theorem handles the remaining state-size branch. -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyEvaluation
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance sourceRepairStateMeasurable : MeasurableSpace State := ⊤

/-- The manuscript beta-radius event for all positive sample sizes when
S≥2 and its universal confidence constant is at least 8. -/
theorem policyEvaluation_source_radius_all_positive_samples
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (N : ℕ) (hN : 0 < N) (δ C₀ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hC₀ : 8 ≤ C₀)
    (hS : (2 : ℝ) ≤ (Fintype.card State : ℝ)) :
    1 - δ < (samplingLaw M π N).real {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
        3 * Real.sqrt (8 *
          (C₀ * Real.log ((Fintype.card State : ℝ) *
            (policyEvaluationDepth M : ℝ) / δ)) /
          ((1 - M.discount) ^ 3 * N))} := by
  let μ := samplingLaw M π N
  let target : Set (Samples State N) := {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
        3 * Real.sqrt (8 *
          (C₀ * Real.log ((Fintype.card State : ℝ) *
            (policyEvaluationDepth M : ℝ) / δ)) /
          ((1 - M.discount) ^ 3 * N))}
  have hprob := valueEstimator_all_positive_samples_source_radius M π N hN δ hδ hδ1
  have hsub := policyEvaluation_api_radius_event_subset_source_beta_radius
    M π N hN δ C₀ hδ hδ1 hC₀ hS
  exact hprob.trans_le (measureReal_mono hsub (measure_ne_top μ target))

end StatisticalRL.ModelBasedPolicyEvaluation

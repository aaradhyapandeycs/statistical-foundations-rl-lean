import Formalization.Generative.PolicyEvaluationSourceTheorem

/-! Source-shaped universal constant wrapper, with its witness chosen before
all finite source carriers, models, policies, sample counts and accuracies. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyEvaluation
local instance universalConstantFinMeasurable (S : ℕ) : MeasurableSpace (Fin S) := ⊤

/-- The printed policy-evaluation assertion with a globally universal constant
and its original non-strict probability conclusion on labeled finite carriers. -/
theorem policyEvaluation_universal_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (S A N : ℕ)
      (M : DiscountedMDP (Fin S) (Fin A)) (π : StationaryPolicy (Fin S) (Fin A))
      (δ ε : ℝ), 0 < δ → δ < 1 → 0 < ε → ε ≤ 1 / (1 - M.discount) →
      c * Real.log (S / (δ * (1 - M.discount))) / ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N →
      ∃ hN : 0 < N, 1 - δ ≤ (samplingLaw M π N).real {data |
        ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤ ε} := by
  refine ⟨720, by norm_num, ?_⟩
  intro S A N M π δ ε hδ hδ1 hε hεmax hbound
  obtain ⟨hN, hs⟩ := valueEstimator_source_sample_bound M π N δ ε hδ hδ1 hε hεmax
    (by simpa only [Fintype.card_fin] using hbound)
  exact ⟨hN, hs.le⟩

end StatisticalRL.ModelBasedPolicyEvaluation

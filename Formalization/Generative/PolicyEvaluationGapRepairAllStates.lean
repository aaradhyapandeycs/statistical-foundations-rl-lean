import Formalization.Generative.PolicyEvaluationGapRepairSource
import Formalization.Generative.PolicyEvaluationSampleAssembly

/-! Source-radius result for every nonempty finite state space, combining the
multi-state beta comparison with the one-state exactness branch. -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyEvaluation
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance allStatesRepairMeasurable : MeasurableSpace State := ⊤

/-- The source beta-radius event holds for every nonempty finite state space
and every positive sample count. One state is exact; the multi-state case uses
the all-sample source-radius comparison. -/
theorem policyEvaluation_source_radius_all_states_positive_samples
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (N : ℕ) (hN : 0 < N) (δ C₀ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hC₀ : 8 ≤ C₀) :
    1 - δ < (samplingLaw M π N).real {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
        3 * Real.sqrt (8 *
          (C₀ * Real.log ((Fintype.card State : ℝ) *
            (policyEvaluationDepth M : ℝ) / δ)) /
          ((1 - M.discount) ^ 3 * N))} := by
  classical
  by_cases hS : 2 ≤ Fintype.card State
  · have hSr : (2 : ℝ) ≤ (Fintype.card State : ℝ) := by exact_mod_cast hS
    exact policyEvaluation_source_radius_all_positive_samples M π N hN δ C₀
      hδ hδ1 hC₀ hSr
  · have hcard : Fintype.card State ≤ 1 := by omega
    letI : Subsingleton State := Fintype.card_le_one_iff_subsingleton.mp hcard
    have htarget : {data : Samples State N |
        ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
          3 * Real.sqrt (8 *
            (C₀ * Real.log ((Fintype.card State : ℝ) *
              (policyEvaluationDepth M : ℝ) / δ)) /
            ((1 - M.discount) ^ 3 * N))} = Set.univ := by
      ext data
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [valueEstimator_eq_true_of_subsingleton M π N hN data, sub_self, norm_zero]
      positivity
    rw [htarget, probReal_univ]
    linarith

end StatisticalRL.ModelBasedPolicyEvaluation

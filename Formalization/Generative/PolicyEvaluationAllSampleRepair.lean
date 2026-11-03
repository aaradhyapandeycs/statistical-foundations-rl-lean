import Formalization.Generative.PolicyEvaluationHighSample
import Formalization.Generative.PolicyEvaluationRecursiveUnroll

/-! All-positive-sample actual-law policy-evaluation radius helper. The
deterministic small-sample branch combines with the high-sample API at the
same radius. -/

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyEvaluation
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance allSampleStateDecidable : DecidableEq State := Classical.decEq State
local instance allSampleStateMeasurable : MeasurableSpace State := ⊤

/-- The displayed policy-evaluation radius holds at every positive sample
size: below the cutoff it follows pathwise from bounded values, above it from
the actual empirical concentration event. -/
theorem valueEstimator_all_positive_samples_source_radius
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M π N).real {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
        3 * Real.sqrt (8 * policyEvaluationBeta M δ /
          ((1 - M.discount) ^ 3 * N))} := by
  classical
  let β := policyEvaluationBeta M δ
  have hgap : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hβ : 0 ≤ β := by
    have hlog := auxiliaryRecursionLog_pos M (policyEvaluationDepth M) δ hδ hδ1
    dsimp [β, policyEvaluationBeta]
    positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hsmall : (N : ℝ) ≤ 72 * β / (1 - M.discount)
  · have htarget : {data : Samples State N |
        ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
          3 * Real.sqrt (8 * β / ((1 - M.discount) ^ 3 * N))} = Set.univ := by
      ext data
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [valueEstimator_eq_trajectory]
      exact trajectoryValue_small_sample_bound M (empiricalModel M π N hN data) π
        rfl β N hβ hNr hsmall
    change 1 - δ < (samplingLaw M π N).real {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
        3 * Real.sqrt (8 * β / ((1 - M.discount) ^ 3 * N))}
    rw [htarget, probReal_univ]
    linarith
  · have hNbound : 64 * policyEvaluationBeta M δ / (1 - M.discount) ≤ N := by
      have hratio : 0 ≤ β / (1 - M.discount) := div_nonneg hβ hgap.le
      have hlarge : 72 * β / (1 - M.discount) < N := lt_of_not_ge hsmall
      have h64 : 64 * β / (1 - M.discount) ≤
          72 * β / (1 - M.discount) := by
        calc
          64 * β / (1 - M.discount) = 64 * (β / (1 - M.discount)) := by ring
          _ ≤ 72 * (β / (1 - M.discount)) :=
            mul_le_mul_of_nonneg_right (by norm_num : (64 : ℝ) ≤ 72) hratio
          _ = 72 * β / (1 - M.discount) := by ring
      exact h64.trans hlarge.le
    exact valueEstimator_high_sample M π N hN δ hδ hδ1 hNbound

end StatisticalRL.ModelBasedPolicyEvaluation

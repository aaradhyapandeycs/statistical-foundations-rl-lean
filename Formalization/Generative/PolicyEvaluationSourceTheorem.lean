import Formalization.Generative.PolicyEvaluationHighSample
import Formalization.Generative.PolicyEvaluationSampleAssembly

/-!
# Source-shaped policy-evaluation sample theorem

Assembly of the exact empirical estimator, actual sampling law, and the
concrete universal constant 720. Staged dependencies and this theorem
require independent review and integrated-export validation.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyEvaluation

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance sourceTheoremStateMeasurable : MeasurableSpace State := ⊤

/-- The source's printed budget is strictly positive, so any natural sample
count meeting it is positive; this proof is the estimator's required witness. -/
theorem source_sample_count_pos (M : DiscountedMDP State Action)
    (N : ℕ) (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε)
    (hNbound : 720 * Real.log (Fintype.card State / (δ * (1 - M.discount))) /
      ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N) : 0 < N := by
  letI : Nonempty State := M.state_nonempty
  let h := 1 - M.discount
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hh1 : h ≤ 1 := by dsimp [h]; linarith [M.discount_nonneg]
  have hS : (1 : ℝ) ≤ Fintype.card State := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hδh : 0 < δ * h := mul_pos hδ hh
  have hδh1 : δ * h < 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hh1) hδ.le]
  have hlog : 0 < Real.log (Fintype.card State / (δ * h)) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hδh).2
    linarith
  have hb : 0 < 720 * Real.log (Fintype.card State / (δ * h)) / (h ^ 3 * ε ^ 2) := by positivity
  have hn : (0 : ℝ) < N := hb.trans_le hNbound
  exact_mod_cast hn

/-- Actual-law policy evaluation with the source's printed logarithm and a
concrete universal constant. The positive sample witness is derived from the
budget, not assumed as a separate mathematical condition. -/
theorem valueEstimator_source_sample_bound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (δ ε : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε)
    (hεmax : ε ≤ 1 / (1 - M.discount))
    (hNbound : 720 * Real.log (Fintype.card State / (δ * (1 - M.discount))) /
      ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N) :
    ∃ hN : 0 < N, 1 - δ < (samplingLaw M π N).real {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤ ε} := by
  classical
  letI : Nonempty State := M.state_nonempty
  let hN : 0 < N := source_sample_count_pos M N δ ε hδ hδ1 hε hNbound
  refine ⟨hN, ?_⟩
  by_cases hS : Fintype.card State ≤ 1
  · letI : Subsingleton State := Fintype.card_le_one_iff_subsingleton.mp hS
    have heq : {data : Samples State N |
        ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤ ε} = Set.univ := by
      ext data
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [valueEstimator_eq_true_of_subsingleton M π N hN data, sub_self, norm_zero]
      exact hε.le
    rw [heq, probReal_univ]
    linarith
  · have hS2 : (2 : ℝ) ≤ Fintype.card State := by
      have hn : 2 ≤ Fintype.card State := by omega
      exact_mod_cast hn
    let h := 1 - M.discount
    have hh : 0 < h := sub_pos.mpr M.discount_lt_one
    have hh1 : h ≤ 1 := by dsimp [h]; linarith [M.discount_nonneg]
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hb := source_sample_budget_from_printed_log h (Fintype.card State) δ ε N
      hh hh1 hS2 hδ hδ1 hε hεmax hn hNbound
    have hb' : 64 * policyEvaluationBeta M δ / h ≤ N ∧
        3 * Real.sqrt (8 * policyEvaluationBeta M δ / (h ^ 3 * N)) ≤ ε := by
      simpa only [policyEvaluationBeta, policyEvaluationDepth, auxiliaryRecursionLog,
        Nat.cast_add, Nat.cast_one] using hb
    let μ := samplingLaw M π N
    let good : Set (Samples State N) := {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤
        3 * Real.sqrt (8 * policyEvaluationBeta M δ / (h ^ 3 * N))}
    let target : Set (Samples State N) := {data |
      ‖valueEstimator M π N hN data - M.trajectoryExpectedValue π‖ ≤ ε}
    have hs : 1 - δ < μ.real good := valueEstimator_high_sample M π N hN δ hδ hδ1 hb'.1
    have hsub : good ⊆ target := by intro data hd; exact hd.trans hb'.2
    exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ target))

end StatisticalRL.ModelBasedPolicyEvaluation

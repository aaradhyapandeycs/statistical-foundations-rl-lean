import Formalization.Generative.PolicyLearningAllRowBernstein
import Formalization.Generative.PolicyLearningVarianceTransfer
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Transfer the actual all-grid Bernstein event to the data-selected empirical
optimal value, with no independence assertion for the selected grid index. -/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance optimalResidualStateMeasurable : MeasurableSpace State := ⊤

/-- The source beta always exceeds the numerical threshold used by the
variance-transfer arithmetic. -/
theorem leaveOneOutBeta_ge_four (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    4 ≤ leaveOneOutBeta M N δ := by
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let S : ℝ := Fintype.card State
  let A : ℝ := Fintype.card Action
  let h := 1 - M.discount
  have hS : 1 ≤ S := by dsimp [S]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hA : 1 ≤ A := by dsimp [A]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hh1 : h ≤ 1 := by dsimp [h]; linarith [M.discount_nonneg]
  have hSA : 1 ≤ S * A := by nlinarith [mul_nonneg (sub_nonneg.mpr hS) (sub_nonneg.mpr hA)]
  have hSAN : 1 ≤ S * A * N := by
    have hh' := mul_le_mul hSA hN1 (by positivity : 0 ≤ (1 : ℝ)) (by positivity : 0 ≤ S * A)
    nlinarith
  have hhd : h * δ ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hh1) (sub_nonneg.mpr hδ1.le)]
  have harg : (16 : ℝ) ≤ 16 * S * A * N / (h * δ) := by
    apply (le_div_iff₀ (mul_pos hh hδ)).2
    nlinarith
  have hlog16 : 2 ≤ Real.log 16 := by
    have heq : Real.log 16 = 4 * Real.log 2 := by
      calc
        _ = Real.log ((2 : ℝ) ^ (4 : ℕ)) := by norm_num
        _ = _ := by rw [Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 16) harg
  change 4 ≤ 2 * Real.log (16 * S * A * N / (h * δ))
  linarith

/-- The source's all-state-action residual bound for the actual, data-selected
empirical optimal value, on one event of probability greater than 1−δ/2. -/
theorem empiricalOptimalValue_allRows_residual (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ / 2 < (samplingLaw M N).real {data |
      ∀ (x : State) (a : Action),
      |(empiricalRow N hN data x a).expectation (valueEstimator M N hN data) -
        (M.transition x a).expectation (valueEstimator M N hN data)| ≤
      Real.sqrt (leaveOneOutBeta M N δ / N) *
        Real.sqrt ((M.transition x a).variance (valueEstimator M N hN data)) +
      2 * leaveOneOutBeta M N δ / (N * (1 - M.discount))} := by
  let μ := samplingLaw M N
  let β := leaveOneOutBeta M N δ
  let h := 1 - M.discount
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hβ : 4 ≤ β := leaveOneOutBeta_ge_four M N hN δ hδ hδ1
  let good : Set (Samples State Action N) := {data |
      ∀ (x : State) (a : Action) (i : Fin (N+1)),
      |(empiricalRow N hN data x a).expectation (leaveOneOutGridValue M N hN x i data) -
        (M.transition x a).expectation (leaveOneOutGridValue M N hN x i data)| ≤
      Real.sqrt (β / N) * Real.sqrt ((M.transition x a).variance (leaveOneOutGridValue M N hN x i data)) +
      β / (3 * N * h)}
  have hs : 1 - δ / 2 < μ.real good := leaveOneOutGrid_allRows_bernstein M N hN δ hδ hδ1
  let target : Set (Samples State Action N) := {data |
      ∀ (x : State) (a : Action),
      |(empiricalRow N hN data x a).expectation (valueEstimator M N hN data) -
        (M.transition x a).expectation (valueEstimator M N hN data)| ≤
      Real.sqrt (β / N) * Real.sqrt ((M.transition x a).variance (valueEstimator M N hN data)) +
      2 * β / (N * h)}
  have hsub : good ⊆ target := by
    intro data hd x a
    obtain ⟨i, hi⟩ := empirical_absorbingGrid_covers_valueEstimator M N hN data x
    have hcover : ‖valueEstimator M N hN data - leaveOneOutGridValue M N hN x i data‖ ≤
        1 / ((N : ℝ) * h) := by
      rw [leaveOneOutGridValue_eq_gridValue]
      exact hi
    have hgrid := hd x a i
    exact FiniteDistribution.bernstein_radius_transfer_source (M.transition x a)
      (empiricalRow N hN data x a) (valueEstimator M N hN data)
      (leaveOneOutGridValue M N hN x i data) N hN h β hh hβ hcover hgrid
  exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ target))

end StatisticalRL.ModelBasedPolicyLearning

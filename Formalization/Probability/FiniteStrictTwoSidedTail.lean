import Formalization.Probability.FiniteStrictSubgaussianTail

/-! finite-space strict two-sided Chernoff conversion. -/
namespace StatisticalRL
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem subgaussianRadius_exp_eq
    (c : ℝ≥0) (hc : 0 < c) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Real.exp (-(Real.sqrt (2 * (c : ℝ) * Real.log (1 / δ)))^2 / (2 * c)) = δ := by
  have hc' : 0 < (c : ℝ) := by exact_mod_cast hc
  have hratio : 1 < 1 / δ := (lt_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hlog : 0 < Real.log (1 / δ) := Real.log_pos hratio
  have hs := Real.sq_sqrt (show 0 ≤ 2 * (c : ℝ) * Real.log (1 / δ) by positivity)
  rw [hs]
  have he : -(2 * (c : ℝ) * Real.log (1 / δ)) / (2 * c) =
      -Real.log (1 / δ) := by field_simp [ne_of_gt hc']
  rw [he, one_div, Real.log_inv, neg_neg, Real.exp_log hδ]

theorem HasSubgaussianMGF.measure_abs_le_sqrt_gt_of_finite
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (c : ℝ≥0) (hc : 0 < c)
    (hX : ProbabilityTheory.HasSubgaussianMGF X c μ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - 2 * δ < μ.real {ω | |X ω| ≤ Real.sqrt (2 * (c : ℝ) * Real.log (1 / δ))} := by
  classical
  let r := Real.sqrt (2 * (c : ℝ) * Real.log (1 / δ))
  have hc' : 0 < (c : ℝ) := by exact_mod_cast hc
  have hratio : 1 < 1 / δ := (lt_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hlog : 0 < Real.log (1 / δ) := Real.log_pos hratio
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hpos : μ.real {ω | r < X ω} < δ := by
    have ht := StatisticalRL.HasSubgaussianMGF.measure_gt_lt_of_finite μ X c hc hX r hr
    simpa only [r, subgaussianRadius_exp_eq c hc δ hδ hδ1] using ht
  have hneg : μ.real {ω | r < -X ω} < δ := by
    have ht := StatisticalRL.HasSubgaussianMGF.measure_gt_lt_of_finite μ (-X) c hc hX.neg r hr
    simpa only [Pi.neg_apply, r, subgaussianRadius_exp_eq c hc δ hδ hδ1] using ht
  let good : Set Ω := {ω | |X ω| ≤ r}
  have hsub : goodᶜ ⊆ {ω | r < X ω} ∪ {ω | r < -X ω} := by
    intro ω hω
    have ha : r < |X ω| := lt_of_not_ge hω
    by_cases hx : 0 ≤ X ω
    · left
      simpa only [Set.mem_setOf_eq, abs_of_nonneg hx] using ha
    · right
      simpa only [Set.mem_setOf_eq, abs_of_neg (lt_of_not_ge hx)] using ha
  have hbad : μ.real goodᶜ < 2 * δ :=
    ((measureReal_mono hsub (measure_ne_top μ _)).trans
      (measureReal_union_le _ _)).trans_lt (by linarith)
  have hcompl := measureReal_add_measureReal_compl (μ := μ)
    ((Set.to_countable good).measurableSet)
  simp only [probReal_univ] at hcompl
  change 1 - 2 * δ < μ.real good
  linarith

end StatisticalRL

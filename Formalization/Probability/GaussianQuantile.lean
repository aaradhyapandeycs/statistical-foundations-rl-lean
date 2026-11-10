import Formalization.Probability.SteinGaussian
import Mathlib.Probability.CDF

/-!
# Two-sided quantiles of centered real Gaussians

General facts about the standard normal distribution function `stdCDF` (from
`SteinGaussian.lean`) and the two-sided quantile of `|X|`, `X ∼ N(0, v)`:

* `stdCDF_zero`, `stdCDF_neg`, `strictMono_stdCDF`, `tendsto_stdCDF_atTop`;
* `gaussianReal_real_Icc_neg_self`: `N(0,1)[−c, c] = 2Φ(c) − 1`;
* `gaussianReal_abs_le_mul_sqrt`, `two_mul_stdCDF_sub_one_le_gaussianReal`:
  `N(0, v){|x| ≤ z√v} = 2Φ(z) − 1` (`v ≠ 0`), resp. `≥` for every `v ≥ 0`;
* `le_mul_sqrt_of_quantile`: anything at most the lower `(1 − α)`-quantile is `≤ z√v`;
* `exists_two_mul_stdCDF_sub_one_ge`, `exists_two_mul_stdCDF_sub_one_eq`: two-sided levels;
* `isQuantile_mul_sqrt`: `z√v` is the exact lower `(1 − α)`-quantile of `|N(0, v)|`, for every
  `v ≥ 0` including the point mass `v = 0`.

Infrastructure (used by the C47(2) evidence in `TDInference/Confidence/PrintedRectangleEvidence.lean`); no
source result is stated here.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace StatisticalRL.Probability.Stein

theorem stdCDF_zero : stdCDF 0 = 1 / 2 := by
  have h1 := stdCDF_add_stdTail 0
  have h2 := stdCDF_eq_stdTail_neg 0
  rw [neg_zero] at h2
  linarith

theorem stdCDF_neg (z : ℝ) : stdCDF (-z) = 1 - stdCDF z := by
  rw [stdCDF_eq_stdTail_neg, neg_neg, stdTail_eq]

theorem strictMono_stdCDF : StrictMono stdCDF :=
  strictMono_of_deriv_pos fun x ↦ by rw [(hasDerivAt_stdCDF x).deriv]; exact stdPDF_pos x

theorem tendsto_stdCDF_atTop : Tendsto stdCDF atTop (𝓝 1) :=
  (tendsto_cdf_atTop (μ := gaussianReal 0 1)).congr fun x ↦ by
    rw [cdf_eq_real, gaussianReal_real_Iic]

/-- `N(0,1)[−c, c] = 2Φ(c) − 1` for `c ≥ 0`. -/
theorem gaussianReal_real_Icc_neg_self {c : ℝ} (hc : 0 ≤ c) :
    (gaussianReal 0 1).real (Set.Icc (-c) c) = 2 * stdCDF c - 1 := by
  haveI := noAtoms_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [← measureReal_congr (Ioc_ae_eq_Icc (μ := gaussianReal 0 1) (a := -c) (b := c)),
    ← Set.Iic_diff_Iic, measureReal_diff (Set.Iic_subset_Iic.2 (by linarith)) measurableSet_Iic,
    gaussianReal_real_Iic, gaussianReal_real_Iic, stdCDF_neg]
  ring

/-- `N(0, v)` is the law of `√v · X`, `X ∼ N(0, 1)`. -/
private theorem gaussianReal_eq_map_sqrt_mul (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun x ↦ Real.sqrt v * x) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · ext; simp

/-- For `v ≠ 0` and `z ≥ 0`: `N(0, v){x | |x| ≤ z√v} = 2Φ(z) − 1`. -/
theorem gaussianReal_abs_le_mul_sqrt {v : ℝ≥0} (hv : v ≠ 0) {z : ℝ} (hz : 0 ≤ z) :
    (gaussianReal 0 v).real {x | |x| ≤ z * Real.sqrt v} = 2 * stdCDF z - 1 := by
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  rw [gaussianReal_eq_map_sqrt_mul v,
    map_measureReal_apply (by fun_prop) (measurableSet_le (by fun_prop) (by fun_prop)),
    ← gaussianReal_real_Icc_neg_self hz]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc, abs_mul, abs_of_pos hs]
  have key : Real.sqrt v * |y| ≤ z * Real.sqrt v ↔ |y| ≤ z := by
    constructor
    · intro h
      exact le_of_mul_le_mul_right (by linarith [mul_comm (Real.sqrt v) |y|]) hs
    · intro h
      nlinarith
  rw [key, abs_le]

/-- For every `v ≥ 0` (including `v = 0`, the point mass) and `z ≥ 0`:
`2Φ(z) − 1 ≤ N(0, v){x | |x| ≤ z√v}`. -/
theorem two_mul_stdCDF_sub_one_le_gaussianReal (v : ℝ≥0) {z : ℝ} (hz : 0 ≤ z) :
    2 * stdCDF z - 1 ≤ (gaussianReal 0 v).real {x | |x| ≤ z * Real.sqrt v} := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var]
    have hmem : (0 : ℝ) ∈ {x : ℝ | |x| ≤ z * Real.sqrt ((0 : ℝ≥0) : ℝ)} := by simp
    rw [measureReal_def, Measure.dirac_apply_of_mem hmem, ENNReal.toReal_one]
    linarith [stdCDF_le_one z]
  · rw [gaussianReal_abs_le_mul_sqrt hv hz]

/-- **Quantile bound.** If no `R' < R` has `N(0, v){|x| ≤ R'} ≥ 1 − α` (i.e. `R` is at most the
lower `(1 − α)`-quantile of `|N(0, v)|`) and `2Φ(z) − 1 ≥ 1 − α` with `z ≥ 0`, then `R ≤ z√v`. -/
theorem le_mul_sqrt_of_quantile (v : ℝ≥0) {α z R : ℝ} (hz : 0 ≤ z)
    (hzα : 1 - α ≤ 2 * stdCDF z - 1)
    (hR : ∀ R' : ℝ, R' < R → (gaussianReal 0 v).real {x | |x| ≤ R'} < 1 - α) :
    R ≤ z * Real.sqrt v := by
  by_contra h
  push_neg at h
  have h1 := hR _ h
  linarith [two_mul_stdCDF_sub_one_le_gaussianReal v hz]

/-- A level `z ≥ 0` with `2Φ(z) − 1 ≥ 1 − α`, for every `α > 0`. -/
theorem exists_two_mul_stdCDF_sub_one_ge {α : ℝ} (hα : 0 < α) :
    ∃ z, 0 ≤ z ∧ 1 - α ≤ 2 * stdCDF z - 1 := by
  obtain ⟨z, hz1, hz0⟩ :=
    ((tendsto_stdCDF_atTop.eventually (lt_mem_nhds (by linarith : 1 - α / 2 < 1))).and
      (eventually_ge_atTop 0)).exists
  exact ⟨z, hz0, by linarith⟩

/-- The exact two-sided level: `z ≥ 0` with `2Φ(z) − 1 = 1 − α`, for `0 < α < 1`. -/
theorem exists_two_mul_stdCDF_sub_one_eq {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ z, 0 ≤ z ∧ 2 * stdCDF z - 1 = 1 - α := by
  obtain ⟨b, hb0, hb⟩ := exists_two_mul_stdCDF_sub_one_ge hα0
  have hmem : 1 - α / 2 ∈ Set.Icc (stdCDF 0) (stdCDF b) := by
    rw [stdCDF_zero]; constructor <;> linarith
  obtain ⟨z, hz, hzeq⟩ :=
    intermediate_value_Icc hb0 continuous_stdCDF.continuousOn hmem
  exact ⟨z, hz.1, by rw [hzeq]; ring⟩

/-- **The exact quantile.** For every `v ≥ 0`, `z ≥ 0` with `2Φ(z) − 1 = 1 − α` and `α < 1`,
`R = z√v` is the lower `(1 − α)`-quantile of `|N(0, v)|`. -/
theorem isQuantile_mul_sqrt (v : ℝ≥0) {α z : ℝ} (hz : 0 ≤ z) (hzα : 2 * stdCDF z - 1 = 1 - α)
    (hα1 : α < 1) :
    1 - α ≤ (gaussianReal 0 v).real {x | |x| ≤ z * Real.sqrt v} ∧
      ∀ R' : ℝ, R' < z * Real.sqrt v → (gaussianReal 0 v).real {x | |x| ≤ R'} < 1 - α := by
  refine ⟨hzα ▸ two_mul_stdCDF_sub_one_le_gaussianReal v hz, fun R' hR' ↦ ?_⟩
  rcases lt_or_ge R' 0 with hneg | hnn
  · have he : {x : ℝ | |x| ≤ R'} = ∅ := Set.eq_empty_of_forall_notMem fun x hx ↦ by
      simp only [Set.mem_setOf_eq] at hx
      linarith [abs_nonneg x]
    rw [he, measureReal_empty]
    linarith
  · rcases eq_or_ne v 0 with rfl | hv
    · simp at hR'
      linarith
    have hs : 0 < Real.sqrt v := Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
    have hR'eq : R' = R' / Real.sqrt v * Real.sqrt v := by field_simp
    rw [hR'eq, gaussianReal_abs_le_mul_sqrt hv (div_nonneg hnn hs.le), ← hzα]
    have hlt : R' / Real.sqrt v < z := by rw [div_lt_iff₀ hs]; exact hR'
    linarith [strictMono_stdCDF hlt]

end StatisticalRL.Probability.Stein

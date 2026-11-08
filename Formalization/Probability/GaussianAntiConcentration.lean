import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Gaussian anti-concentration on slabs

Reusable bounds (pinned Mathlib has no sup bound for the Gaussian density and no `IsGaussian`
instance for `Measure.pi`; these lemmas avoid both):

* `gaussianPDFReal_le_inv_sqrt`: the `N(m, v)` density is at most `1/√(2πv)`.
* `gaussianReal_Icc_le`: `N(m, v)([a, b]) ≤ (b - a)/√(2πv)` for `v ≠ 0`.
* `gaussianReal_abs_affine_le`: `N(m, v){y : |c y + b| ≤ δ} ≤ 2δ/(|c|√(2πv))` for `c ≠ 0`.
* `measure_pi_le_of_slice_le`: for a product of probability measures, a uniform bound on the
  one-coordinate slices of a measurable set bounds the set (Fubini via `lmarginal`).
* `stdGaussianPi_abs_linear_le`: for `Z` with i.i.d. `N(0,1)` coordinates, any linear form
  `∑ᵢ cᵢ Zᵢ` and any `j` with `c_j ≠ 0`, `P(|∑ᵢ cᵢ Zᵢ - b| ≤ δ) ≤ 2δ/(|c_j|√(2π))`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatisticalRL.Probability

/-- The Gaussian density is bounded by its value at the mean, `1/√(2πv)`. -/
theorem gaussianPDFReal_le_inv_sqrt (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x ≤ (√(2 * π * v))⁻¹ := by
  rw [gaussianPDFReal]
  refine mul_le_of_le_one_right (inv_nonneg.2 (Real.sqrt_nonneg _)) ?_
  rw [Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

/-- `N(m, v)([a, b]) ≤ (b - a)/√(2πv)` for `v ≠ 0`. -/
theorem gaussianReal_Icc_le (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (a b : ℝ) :
    gaussianReal m v (Set.Icc a b) ≤ ENNReal.ofReal ((√(2 * π * v))⁻¹ * (b - a)) := by
  rw [gaussianReal_of_var_ne_zero _ hv, withDensity_apply _ measurableSet_Icc]
  calc ∫⁻ x in Set.Icc a b, gaussianPDF m v x
      ≤ ∫⁻ _ in Set.Icc a b, ENNReal.ofReal ((√(2 * π * v))⁻¹) :=
        setLIntegral_mono measurable_const fun x _ ↦
          ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_inv_sqrt m v x)
    _ = ENNReal.ofReal ((√(2 * π * v))⁻¹ * (b - a)) := by
        rw [setLIntegral_const, Real.volume_Icc,
          ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _))]

/-- Anti-concentration of `N(m, v)` on an affine slab: for `c ≠ 0`,
`N(m, v){y : |c y + b| ≤ δ} ≤ 2δ/(|c|√(2πv))`. -/
theorem gaussianReal_abs_affine_le (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {c : ℝ} (hc : c ≠ 0)
    (b δ : ℝ) :
    gaussianReal m v {y | |c * y + b| ≤ δ} ≤
      ENNReal.ofReal (2 * δ / (|c| * √(2 * π * v))) := by
  have hca : 0 < |c| := abs_pos.2 hc
  have hsub : {y | |c * y + b| ≤ δ} ⊆ Set.Icc (-(b / c) - δ / |c|) (-(b / c) + δ / |c|) := by
    intro y hy
    have h1 : c * y + b = c * (y + b / c) := by field_simp
    rw [Set.mem_setOf_eq, h1, abs_mul, ← le_div_iff₀' hca] at hy
    rw [Set.mem_Icc]
    constructor <;> linarith [(abs_le.1 hy).1, (abs_le.1 hy).2]
  refine (measure_mono hsub).trans ((gaussianReal_Icc_le m hv _ _).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  field_simp
  ring

/-- Fubini on a finite product of probability measures: if every one-coordinate slice of a
measurable set `S` in coordinate `j` has `μ j`-mass at most `m`, then `S` has mass at most `m`. -/
theorem measure_pi_le_of_slice_le {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {S : Set (∀ i, X i)} (hS : MeasurableSet S) (j : ι) {m : ℝ≥0∞}
    (h : ∀ x : ∀ i, X i, μ j ((fun y ↦ Function.update x j y) ⁻¹' S) ≤ m) :
    Measure.pi μ S ≤ m := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, -⟩
  · simp
  have hf : Measurable (S.indicator (1 : (∀ i, X i) → ℝ≥0∞)) := measurable_one.indicator hS
  rw [← lintegral_indicator_one hS, lintegral_eq_lmarginal_univ x,
    lmarginal_erase' _ hf (Finset.mem_univ j)]
  calc (∫⋯∫⁻_Finset.univ.erase j,
        (fun x ↦ ∫⁻ xⱼ, S.indicator 1 (Function.update x j xⱼ) ∂μ j) ∂μ) x
      ≤ (∫⋯∫⁻_Finset.univ.erase j, (fun _ ↦ m) ∂μ) x := by
        refine lmarginal_mono (fun z ↦ ?_) x
        have hz : (fun xⱼ ↦ S.indicator (1 : (∀ i, X i) → ℝ≥0∞) (Function.update z j xⱼ)) =
            ((fun y ↦ Function.update z j y) ⁻¹' S).indicator 1 := by
          funext y
          simp only [Set.indicator, Set.mem_preimage, Pi.one_apply]; rfl
        simp only
        rw [hz, lintegral_indicator_one (hS.preimage (measurable_update z))]
        exact h z
    _ = m := by
        simp [lmarginal, lintegral_const, measure_univ]

/-- `∑ᵢ cᵢ (update x j y)ᵢ = c_j y + ∑_{i ≠ j} cᵢ xᵢ`. -/
theorem sum_mul_update_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (c x : ι → ℝ) (j : ι) (y : ℝ) :
    ∑ i, c i * Function.update x j y i = c j * y + ∑ i ∈ Finset.univ.erase j, c i * x i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- Anti-concentration of a linear form of i.i.d. standard Gaussians, by conditioning on all
coordinates but one: `P(|∑ᵢ cᵢ Zᵢ - b| ≤ δ) ≤ 2δ/(|c_j|√(2π))` whenever `c_j ≠ 0`. -/
theorem stdGaussianPi_abs_linear_le {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ)
    {j : ι} (hj : c j ≠ 0) (b δ : ℝ) :
    Measure.pi (fun _ : ι ↦ gaussianReal 0 1) {z | |∑ i, c i * z i - b| ≤ δ} ≤
      ENNReal.ofReal (2 * δ / (|c j| * √(2 * π))) := by
  have hmeas : MeasurableSet {z : ι → ℝ | |∑ i, c i * z i - b| ≤ δ} := by
    refine measurableSet_le ?_ measurable_const
    refine (Continuous.measurable ?_)
    fun_prop
  refine measure_pi_le_of_slice_le _ hmeas j fun x ↦ ?_
  have hset : (fun y ↦ Function.update x j y) ⁻¹' {z : ι → ℝ | |∑ i, c i * z i - b| ≤ δ} =
      {y | |c j * y + (∑ i ∈ Finset.univ.erase j, c i * x i - b)| ≤ δ} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, sum_mul_update_eq]
    ring_nf
  rw [hset]
  have h := gaussianReal_abs_affine_le 0 (v := 1) one_ne_zero hj
    (∑ i ∈ Finset.univ.erase j, c i * x i - b) δ
  simpa using h

end StatisticalRL.Probability

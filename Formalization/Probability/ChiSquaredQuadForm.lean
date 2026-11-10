import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Formalization.Probability.StdGaussianPi

/-!
# The `χ²(k)` law and Gaussian quadratic forms

Source: `chapters/inference.tex:207–213` (confidence ellipsoids: "`R` is the `1 − α` quantile of
the `χ²(d)` distribution") and `docs/SOURCE-ISSUES.md` C47(3) (there `d = S = |State|`, and the
ellipsoid threshold is `R`, not `R²`). This file supplies the distributional fact behind the
printed `χ²` calibration; the TD corollary is `TDInference/Confidence/ChiSquareQuantile.lean`.

* `chiSquared k` is the `χ²(k)` law, defined as Mathlib's gamma distribution with shape `k/2` and
  rate `1/2` (`gammaMeasure (k/2) (1/2)`; pinned Mathlib has no `χ²` definition).
* `map_sum_sq_stdGaussianPi`: for `Z` standard Gaussian on `ι → ℝ` (`ι` nonempty), the law of
  `∑ᵢ Zᵢ²` is `χ²(|ι|)`.
* `map_mulVec_stdGaussianPi_quadForm_le`: for an invertible `L` and `Λ = L Lᵀ`, the Gaussian
  `N(0,Λ)` = law of `L Z` gives `N(0,Λ){x | xᵀΛ⁻¹x ≤ q} = χ²(|ι|)(-∞, q]` for every real `q`.

Route (moment generating functions, no density convolution):
* `integral_exp_mul_gammaMeasure`: `∫ e^{tx} dGamma(a,r) = (r/(r−t))^a` for `t < r`
  (Mathlib's `integral_rpow_mul_exp_neg_mul_Ioi`);
* `integral_exp_mul_sq_gaussianReal`: `∫ e^{tx²} dN(0,1) = ((1/2)/(1/2−t))^{1/2}` for `t < 1/2`
  (Mathlib's `integral_gaussian`), so by Fubini over the product measure
  (`integral_fintype_prod_eq_prod`) `∫ e^{t∑zᵢ²} = ((1/2)/(1/2−t))^{k/2}`;
* `ext_of_integral_exp_eq_of_lt`: two finite measures on `ℝ` whose exponential moments are finite
  and agree on a half-line `t < c` with `c > 0` are equal (the complex MGFs are analytic on the
  half-plane `Re z < c` and agree on the real points, hence on the imaginary axis; then
  `Measure.ext_of_charFun`). Integrability is obtained from a nonzero integral value
  (`Integrable.of_integral_ne_zero`).
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Matrix
open scoped ENNReal NNReal

namespace StatisticalRL.Probability

/-! ## The `χ²(k)` law -/

/-- The `χ²(k)` law: the gamma distribution with shape `k/2` and rate `1/2`. It is a probability
measure for `k ≥ 1` (`isProbabilityMeasure_chiSquared`). -/
noncomputable def chiSquared (k : ℕ) : Measure ℝ :=
  gammaMeasure ((k : ℝ) / 2) (1 / 2)

theorem isProbabilityMeasure_chiSquared {k : ℕ} (hk : 0 < k) :
    IsProbabilityMeasure (chiSquared k) :=
  isProbabilityMeasure_gammaMeasure (div_pos (Nat.cast_pos.2 hk) two_pos) (by norm_num)

/-! ## Exponential moments -/

/-- `∫ e^{tx} dGamma(a, r) = (r / (r − t))^a` for `t < r`. -/
theorem integral_exp_mul_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    ∫ x, exp (t * x) ∂gammaMeasure a r = (r / (r - t)) ^ a := by
  have hrt : 0 < r - t := sub_pos.2 ht
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (gammaPDF a r) from (measurable_gammaPDFReal a r).ennreal_ofReal) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ici 0) (fun x hx ↦ by
      rw [mem_Ici, not_le] at hx
      simp [gammaPDFReal, not_le.2 hx]),
    integral_Ici_eq_integral_Ioi,
    setIntegral_congr_fun measurableSet_Ioi
      (g := fun x ↦ r ^ a / Gamma a * (x ^ (a - 1) * exp (-((r - t) * x)))) (fun x hx ↦ ?_),
    integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi ha hrt]
  · have hG : Gamma a ≠ 0 := (Gamma_pos_of_pos ha).ne'
    rw [div_rpow hr.le hrt.le, div_rpow zero_le_one hrt.le, one_rpow]
    have : (r - t) ^ a ≠ 0 := (rpow_pos_of_pos hrt a).ne'
    field_simp
  · simp only [gammaPDFReal, if_pos (le_of_lt (mem_Ioi.1 hx))]
    rw [show exp (-((r - t) * x)) = exp (-(r * x)) * exp (t * x) by
      rw [← exp_add]; ring_nf]
    ring

theorem integrable_exp_mul_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    Integrable (fun x ↦ exp (t * x)) (gammaMeasure a r) :=
  Integrable.of_integral_ne_zero (by
    rw [integral_exp_mul_gammaMeasure ha hr ht]
    exact (rpow_pos_of_pos (div_pos hr (sub_pos.2 ht)) a).ne')

/-- `∫ e^{tx²} dN(0,1) = ((1/2)/(1/2 − t))^{1/2}` for `t < 1/2`. -/
theorem integral_exp_mul_sq_gaussianReal {t : ℝ} (ht : t < 1 / 2) :
    ∫ x, exp (t * x ^ 2) ∂gaussianReal 0 1 = ((1 / 2) / (1 / 2 - t)) ^ (1 / 2 : ℝ) := by
  have hb : 0 < 1 / 2 - t := sub_pos.2 ht
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_congr_ae (g := fun x : ℝ ↦ (√(2 * π))⁻¹ * exp (-(1 / 2 - t) * x ^ 2))
      (ae_of_all _ fun x ↦ ?_), integral_const_mul, integral_gaussian]
  · rw [← sqrt_eq_rpow, ← sqrt_inv, ← sqrt_mul (inv_nonneg.2 (by positivity))]
    congr 1
    have := pi_pos.ne'
    field_simp
  · simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [mul_assoc, ← exp_add]
    ring_nf

variable {ι : Type*} [Fintype ι]

/-- `∫ e^{t ∑ zᵢ²} dN(0, I) = ((1/2)/(1/2 − t))^{|ι|/2}` for `t < 1/2`. -/
theorem integral_exp_mul_sum_sq_stdGaussianPi {t : ℝ} (ht : t < 1 / 2) :
    ∫ z, exp (t * ∑ i, z i ^ 2) ∂stdGaussianPi ι =
      ((1 / 2) / (1 / 2 - t)) ^ ((Fintype.card ι : ℝ) / 2) := by
  have hb : 0 ≤ (1 / 2) / (1 / 2 - t) := (div_pos (by norm_num) (sub_pos.2 ht)).le
  have h : ∀ z : ι → ℝ, exp (t * ∑ i, z i ^ 2) = ∏ i, exp (t * z i ^ 2) := fun z ↦ by
    rw [Finset.mul_sum, exp_sum]
  simp_rw [h]
  have hprod := integral_fintype_prod_eq_prod (μ := fun _ : ι ↦ gaussianReal 0 1)
    (fun (_ : ι) (x : ℝ) ↦ exp (t * x ^ 2))
  simp only at hprod
  rw [hprod]
  simp_rw [integral_exp_mul_sq_gaussianReal ht]
  rw [Finset.prod_const, Finset.card_univ, ← rpow_natCast, ← rpow_mul hb]
  congr 1
  ring

theorem integrable_exp_mul_sum_sq_stdGaussianPi {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun z : ι → ℝ ↦ exp (t * ∑ i, z i ^ 2)) (stdGaussianPi ι) :=
  Integrable.of_integral_ne_zero (by
    rw [integral_exp_mul_sum_sq_stdGaussianPi ht]
    exact (rpow_pos_of_pos (div_pos (by norm_num) (sub_pos.2 ht)) _).ne')

/-! ## Uniqueness from exponential moments on a half-line -/

/-- Two finite measures on `ℝ` whose exponential moments `∫ e^{tx}` are finite and agree for all
`t < c`, with `c > 0`, are equal. -/
theorem ext_of_integral_exp_eq_of_lt {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : ℝ} (hc : 0 < c) (hμ : ∀ t < c, Integrable (fun x ↦ exp (t * x)) μ)
    (hν : ∀ t < c, Integrable (fun x ↦ exp (t * x)) ν)
    (h : ∀ t < c, ∫ x, exp (t * x) ∂μ = ∫ x, exp (t * x) ∂ν) : μ = ν := by
  set U : Set ℂ := Complex.reLm ⁻¹' Iio c with hU_def
  have hmem : ∀ z : ℂ, z ∈ U ↔ z.re < c := fun z ↦ Iff.rfl
  have hUμ : U ⊆ {z | z.re ∈ interior (integrableExpSet id μ)} := fun z hz ↦
    interior_maximal (fun t ht ↦ hμ t ht) isOpen_Iio ((hmem z).1 hz)
  have hUν : U ⊆ {z | z.re ∈ interior (integrableExpSet id ν)} := fun z hz ↦
    interior_maximal (fun t ht ↦ hν t ht) isOpen_Iio ((hmem z).1 hz)
  have hf := (analyticOnNhd_complexMGF (X := id) (μ := μ)).mono hUμ
  have hg := (analyticOnNhd_complexMGF (X := id) (μ := ν)).mono hUν
  have hU : IsPreconnected U := ((convex_Iio c).linear_preimage Complex.reLm).isPreconnected
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), complexMGF id μ z = complexMGF id ν z := by
    rw [frequently_iff_seq_forall]
    refine ⟨fun n ↦ ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ), ?_, fun n ↦ ?_⟩
    · rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
      · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg.ofReal
      · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero, neg_eq_zero,
          one_div, inv_eq_zero]
        positivity
    · have hlt : -(1 / ((n : ℝ) + 1)) < c :=
        (neg_nonpos.2 (by positivity)).trans_lt hc
      rw [complexMGF_ofReal, complexMGF_ofReal]
      simp only [mgf, id_eq]
      exact congrArg _ (h _ hlt)
  have heq := hf.eqOn_of_preconnected_of_frequently_eq hg hU ((hmem 0).2 (by simpa using hc))
    hfreq
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact heq ((hmem _).2 (by simpa using hc))

/-! ## `∑ Zᵢ² ∼ χ²(k)` -/

/-- **The `χ²(k)` law of a squared standard Gaussian vector.** For `Z` standard Gaussian on
`ι → ℝ` with `ι` nonempty, the law of `∑ᵢ Zᵢ²` is `χ²(|ι|)`. -/
theorem map_sum_sq_stdGaussianPi [Nonempty ι] :
    (stdGaussianPi ι).map (fun z ↦ ∑ i, z i ^ 2) = chiSquared (Fintype.card ι) := by
  have hk : 0 < Fintype.card ι := Fintype.card_pos
  have hk' : 0 < (Fintype.card ι : ℝ) / 2 := div_pos (Nat.cast_pos.2 hk) two_pos
  haveI := isProbabilityMeasure_chiSquared hk
  have hmeas : Measurable (fun z : ι → ℝ ↦ ∑ i, z i ^ 2) := by fun_prop
  haveI : IsProbabilityMeasure ((stdGaussianPi ι).map (fun z ↦ ∑ i, z i ^ 2)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hexp : ∀ t : ℝ, AEStronglyMeasurable (fun x : ℝ ↦ exp (t * x))
      ((stdGaussianPi ι).map (fun z ↦ ∑ i, z i ^ 2)) := fun t ↦
    (by fun_prop : Continuous fun x : ℝ ↦ exp (t * x)).aestronglyMeasurable
  have hint : ∀ t < (1 / 2 : ℝ), ∫ x, exp (t * x) ∂(stdGaussianPi ι).map (fun z ↦ ∑ i, z i ^ 2) =
      ((1 / 2) / (1 / 2 - t)) ^ ((Fintype.card ι : ℝ) / 2) := fun t ht ↦ by
    rw [integral_map hmeas.aemeasurable (hexp t)]
    exact integral_exp_mul_sum_sq_stdGaussianPi ht
  refine ext_of_integral_exp_eq_of_lt (c := 1 / 2) (by norm_num) (fun t ht ↦ ?_)
    (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · exact Integrable.of_integral_ne_zero (by
      rw [hint t ht]
      exact (rpow_pos_of_pos (div_pos (by norm_num) (sub_pos.2 ht)) _).ne')
  · exact integrable_exp_mul_gammaMeasure hk' (by norm_num) ht
  · rw [hint t ht, chiSquared, integral_exp_mul_gammaMeasure hk' (by norm_num) ht]

/-! ## Quadratic forms of Gaussian vectors -/

/-- For invertible `L` and `x = L z`: `xᵀ (L Lᵀ)⁻¹ x = ∑ᵢ zᵢ²`. -/
theorem quadForm_inv_mul_transpose_mulVec [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : IsUnit L.det)
    (z : ι → ℝ) :
    ∑ s, ∑ s', (L *ᵥ z) s * (L *ᵥ z) s' * (L * Lᵀ)⁻¹ s s' = ∑ i, z i ^ 2 := by
  have hLt : IsUnit Lᵀ.det := by rwa [det_transpose]
  have h1 : ∀ x : ι → ℝ, ∑ s, ∑ s', x s * x s' * (L * Lᵀ)⁻¹ s s' =
      x ⬝ᵥ ((L * Lᵀ)⁻¹ *ᵥ x) := fun x ↦ by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun s' _ ↦ by ring
  rw [h1, Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul L hL,
    Matrix.mul_one, ← vecMul_transpose L z, ← dotProduct_mulVec, mulVec_mulVec,
    mul_nonsing_inv _ hLt, one_mulVec]
  simp [dotProduct, sq]

/-- **Gaussian mass of the ellipsoid is the `χ²` cdf.** For invertible `L` and `Λ = L Lᵀ`, the
Gaussian `N(0,Λ)`, realised as the law of `L Z` with `Z` standard Gaussian on `ι → ℝ` (`ι`
nonempty), satisfies `N(0,Λ){x | xᵀΛ⁻¹x ≤ q} = χ²(|ι|)(-∞, q]` for every real `q`. -/
theorem map_mulVec_stdGaussianPi_quadForm_le [Nonempty ι] [DecidableEq ι] (L : Matrix ι ι ℝ)
    (hL : IsUnit L.det) (q : ℝ) :
    (stdGaussianPi ι).map (L *ᵥ ·) {x | ∑ s, ∑ s', x s * x s' * (L * Lᵀ)⁻¹ s s' ≤ q} =
      chiSquared (Fintype.card ι) (Iic q) := by
  have hLm : Measurable (fun z : ι → ℝ ↦ L *ᵥ z) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hS : MeasurableSet {x : ι → ℝ | ∑ s, ∑ s', x s * x s' * (L * Lᵀ)⁻¹ s s' ≤ q} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hsum : Measurable (fun z : ι → ℝ ↦ ∑ i, z i ^ 2) := by fun_prop
  rw [Measure.map_apply hLm hS, ← map_sum_sq_stdGaussianPi, Measure.map_apply hsum measurableSet_Iic]
  congr 1
  ext z
  simp only [mem_preimage, mem_setOf_eq, mem_Iic]
  rw [quadForm_inv_mul_transpose_mulVec L hL z]

/-- The same identity in cdf form: `N(0,Λ).real {xᵀΛ⁻¹x ≤ q} = F_{χ²(|ι|)}(q)`. -/
theorem map_mulVec_stdGaussianPi_quadForm_le_real [Nonempty ι] [DecidableEq ι]
    (L : Matrix ι ι ℝ) (hL : IsUnit L.det) (q : ℝ) :
    ((stdGaussianPi ι).map (L *ᵥ ·)).real {x | ∑ s, ∑ s', x s * x s' * (L * Lᵀ)⁻¹ s s' ≤ q} =
      cdf (chiSquared (Fintype.card ι)) q := by
  haveI := isProbabilityMeasure_chiSquared (Fintype.card_pos (α := ι))
  rw [measureReal_def, map_mulVec_stdGaussianPi_quadForm_le L hL q, cdf_eq_real, measureReal_def]

end StatisticalRL.Probability

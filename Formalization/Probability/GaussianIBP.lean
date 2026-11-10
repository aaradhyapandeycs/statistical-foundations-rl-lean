import Formalization.Probability.StdGaussianPi
import Formalization.Probability.SteinGaussian
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Instances.Matrix

/-!
# Gaussian integration by parts and derivative bounds for Gaussian smoothing

Infrastructure for the all-convex route to Theorem 7.11 (`thm:Berry-Esseen-linear`,
`chapters/inference.tex:132–141`): pure Gaussian derivative bounds for the smoothing step of the
reservoir Lindeberg argument. Nothing here is a source result.

* `integral_smul_gaussianReal_eq_integral_deriv`: the one-dimensional Stein identity
  `E[Z G(Z)] = E[G'(Z)]` for `Z ∼ N(0,1)` and Banach-valued `G` with bounded `G, G'`;
* `integral_apply_smul_eq_integral_hasFDerivAt`, `integral_apply_mul_eq_integral_fderiv`: the
  coordinatewise multivariate Gaussian integration by parts
  `E[Zᵢ g(Z)] = E[∂ᵢ g(Z)]` on `stdGaussianPi ι` (1-D identity + Fubini, splitting off one
  coordinate with `map_update_prod_stdGaussianPi`);
* `gaussSmooth φ L x = E φ(x + L Z)` (rectangular factor `L : Matrix ι ι' ℝ`),
  `iteratedFDeriv_gaussSmooth` (derivatives commute with the smoothing), `contDiff_gaussSmooth`;
* `norm_iteratedFDeriv_gaussSmooth_le_of_rightInv`: if every `h` has a preimage `L w = h` with
  `‖w‖₂ ≤ r ‖h‖`, then `‖Dᵏ (gaussSmooth φ L) x‖ ≤ gaussDerivConst k · rᵏ · sup ‖φ‖`
  (the derivative bound uses only the sup of `φ`, not of its derivatives);
* `norm_iteratedFDeriv_gaussSmooth_le`: the form used by the reservoir step, under `v ‖u‖² ≤ uᵀ (L Lᵀ) u`;
  constant `gaussDerivConst k · |ι|ᵏ · v^{-k/2}`, independent of `ι'`;
* `norm_iteratedFDeriv_gaussSmooth_smul_le`: plain scaling `x ↦ E φ(x + s Z)`, bound
  `gaussDerivConst k · √|ι|ᵏ · sup ‖φ‖ / sᵏ`.

Norms on `ι → ℝ` are the sup norms of the ambient `Pi` type; derivative norms are the operator
norms of `iteratedFDeriv` for them.

Proof of the derivative bound: one derivative is moved onto the Gaussian by integration by parts
(`norm_gaussSmooth_fderiv_le`); for `k` derivatives the Gaussian is split as
`L Z = (L/√2) Z₁ + (L/√2) Z₂` (`gaussSmooth_eq_gaussSmooth_gaussSmooth`), one derivative falls on
`Z₁` and the remaining `k − 1` on the inner smoothing, by induction.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal Matrix

namespace StatisticalRL.Probability

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-! ## One-dimensional Stein identity -/

open Stein in
theorem integrable_mul_stdPDF : Integrable (fun t : ℝ ↦ t * stdPDF t) := by
  refine ((integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul
    (√(2 * π))⁻¹).congr (ae_of_all _ fun t ↦ ?_)
  have : -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 := by ring
  simp only [stdPDF_eq, this]
  ring

omit [CompleteSpace F] in
open Stein in
/-- One-dimensional Gaussian integration by parts, Banach-valued:
`E[Z G(Z)] = E[G'(Z)]` for `Z ∼ N(0,1)`, `G` differentiable with `G, G'` bounded and `G'`
continuous. -/
theorem integral_smul_gaussianReal_eq_integral_deriv {G G' : ℝ → F}
    (hG : ∀ t, HasDerivAt G (G' t) t) (hG'c : Continuous G') {C₀ C₁ : ℝ}
    (hG0 : ∀ t, ‖G t‖ ≤ C₀) (hG1 : ∀ t, ‖G' t‖ ≤ C₁) :
    ∫ t, t • G t ∂(gaussianReal 0 1) = ∫ t, G' t ∂(gaussianReal 0 1) := by
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun t ↦ (hG t).continuousAt
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  have key := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)) (u := stdPDF)
    (u' := fun t ↦ -t * stdPDF t) (v := G) (v' := G') hasDerivAt_stdPDF hG ?_ ?_ ?_
  · simp only [ContinuousLinearMap.lsmul_apply] at key
    have h1 : (fun t : ℝ ↦ gaussianPDFReal 0 1 t • G' t) = fun t ↦ stdPDF t • G' t := rfl
    rw [h1, key, ← integral_neg]
    congr 1
    ext t
    rw [smul_smul, neg_mul, neg_smul, neg_neg, mul_comm]
    rfl
  · refine (integrable_stdPDF.smul_bdd C₁ hG'c.aestronglyMeasurable
      (ae_of_all _ hG1)).congr (ae_of_all _ fun t ↦ ?_)
    simp
  · refine (integrable_mul_stdPDF.neg.smul_bdd C₀ hGc.aestronglyMeasurable
      (ae_of_all _ hG0)).congr (ae_of_all _ fun t ↦ ?_)
    simp
  · refine (integrable_stdPDF.smul_bdd C₀ hGc.aestronglyMeasurable
      (ae_of_all _ hG0)).congr (ae_of_all _ fun t ↦ ?_)
    simp

/-! ## Splitting off one coordinate -/

section Coordinate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem measurable_update_prod (i : ι) :
    Measurable (fun p : (ι → ℝ) × ℝ ↦ Function.update p.1 i p.2) := by
  refine measurable_pi_lambda _ fun j ↦ ?_
  by_cases hj : j = i
  · subst hj
    simpa using measurable_snd
  · simpa [Function.update_of_ne hj] using (measurable_pi_apply j).comp measurable_fst

/-- Resampling coordinate `i` of a standard Gaussian vector by an independent `N(0,1)` keeps the
law. -/
theorem map_update_prod_stdGaussianPi (i : ι) :
    ((stdGaussianPi ι).prod (gaussianReal 0 1)).map
        (fun p : (ι → ℝ) × ℝ ↦ Function.update p.1 i p.2) = stdGaussianPi ι := by
  symm
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [Measure.map_apply (measurable_update_prod i) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ ↦ Function.update p.1 i p.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (Function.update s i Set.univ) ×ˢ s i := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j ↦ ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj
        simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj
        simpa using h2
      · simpa [Function.update_of_ne hj] using h1 j
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have hupd : (fun j ↦ (gaussianReal 0 1) (Function.update s i Set.univ j)) =
      Function.update (fun j ↦ gaussianReal 0 1 (s j)) i 1 := by
    ext1 j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne hj]
  rw [hupd, Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
    Finset.prod_eq_prod_diff_singleton_mul (Finset.mem_univ i)]

omit [CompleteSpace F] in
/-- Integrals over `stdGaussianPi ι` as iterated integrals with coordinate `i` innermost. -/
theorem integral_stdGaussianPi_eq_integral_update {f : (ι → ℝ) → F} (hf : Continuous f)
    (hfi : Integrable f (stdGaussianPi ι)) (i : ι) :
    ∫ z, f z ∂stdGaussianPi ι =
      ∫ z, ∫ t, f (Function.update z i t) ∂(gaussianReal 0 1) ∂stdGaussianPi ι := by
  have hm := measurable_update_prod (ι := ι) i
  have hmap := map_update_prod_stdGaussianPi (ι := ι) i
  have h1 : ∫ z, f z ∂stdGaussianPi ι = ∫ p, f (Function.update p.1 i p.2)
      ∂((stdGaussianPi ι).prod (gaussianReal 0 1)) := by
    conv_lhs => rw [← hmap]
    exact integral_map hm.aemeasurable hf.aestronglyMeasurable
  have hint : Integrable (fun p : (ι → ℝ) × ℝ ↦ f (Function.update p.1 i p.2))
      ((stdGaussianPi ι).prod (gaussianReal 0 1)) := by
    have h := hfi
    rw [← hmap] at h
    exact (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).1 h
  rw [h1, integral_prod _ hint]

omit [CompleteSpace F] in
/-- **Gaussian integration by parts**, coordinatewise and Banach-valued:
`E[Zᵢ g(Z)] = E[g'(Z) eᵢ]` for `g` differentiable with continuous derivative `g'`, `g` and `g'`
bounded. -/
theorem integral_apply_smul_eq_integral_hasFDerivAt {g : (ι → ℝ) → F}
    {g' : (ι → ℝ) → (ι → ℝ) →L[ℝ] F} (hg : ∀ z, HasFDerivAt g (g' z) z) (hg'c : Continuous g')
    {C₀ C₁ : ℝ} (hg0 : ∀ z, ‖g z‖ ≤ C₀) (hg1 : ∀ z, ‖g' z‖ ≤ C₁) (i : ι) :
    ∫ z, z i • g z ∂stdGaussianPi ι = ∫ z, g' z (Pi.single i 1) ∂stdGaussianPi ι := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun z ↦ (hg z).continuousAt
  have hi1 : Integrable (fun z : ι → ℝ ↦ z i • g z) (stdGaussianPi ι) :=
    (integrable_apply_stdGaussianPi i).smul_bdd C₀ hgc.aestronglyMeasurable (ae_of_all _ hg0)
  have hc2 : Continuous (fun z ↦ g' z (Pi.single i 1)) := hg'c.clm_apply continuous_const
  have hi2 : Integrable (fun z ↦ g' z (Pi.single i 1)) (stdGaussianPi ι) :=
    Integrable.of_bound hc2.aestronglyMeasurable (C₁ * ‖(Pi.single i 1 : ι → ℝ)‖)
      (ae_of_all _ fun z ↦ (g' z).le_of_opNorm_le (hg1 z) _)
  rw [integral_stdGaussianPi_eq_integral_update ((continuous_apply i).smul hgc) hi1 i,
    integral_stdGaussianPi_eq_integral_update hc2 hi2 i]
  congr 1
  ext z
  simp only [Function.update_self]
  have hupd : ∀ t, HasDerivAt (fun t ↦ g (Function.update z i t))
      (g' (Function.update z i t) (Pi.single i 1)) t :=
    fun t ↦ (hg _).comp_hasDerivAt t (hasDerivAt_update z i t)
  have hupdc : Continuous (fun t : ℝ ↦ Function.update z i t) :=
    continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_update z i t).continuousAt
  exact integral_smul_gaussianReal_eq_integral_deriv hupd
    (hg'c.comp hupdc |>.clm_apply continuous_const) (fun t ↦ hg0 _)
    (fun t ↦ (g' _).le_of_opNorm_le (hg1 _) _)

omit [CompleteSpace F] in
/-- Directional form: `E[⟨w, Z⟩ g(Z)] = E[g'(Z) w]`. -/
theorem integral_sum_mul_smul_eq_integral_hasFDerivAt {g : (ι → ℝ) → F}
    {g' : (ι → ℝ) → (ι → ℝ) →L[ℝ] F} (hg : ∀ z, HasFDerivAt g (g' z) z) (hg'c : Continuous g')
    {C₀ C₁ : ℝ} (hg0 : ∀ z, ‖g z‖ ≤ C₀) (hg1 : ∀ z, ‖g' z‖ ≤ C₁) (w : ι → ℝ) :
    ∫ z, (∑ j, w j * z j) • g z ∂stdGaussianPi ι = ∫ z, g' z w ∂stdGaussianPi ι := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun z ↦ (hg z).continuousAt
  have hw : w = ∑ j, w j • (Pi.single j (1 : ℝ) : ι → ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hexp : ∀ z, g' z w = ∑ j, w j • g' z (Pi.single j 1) := by
    intro z
    conv_lhs => rw [hw]
    simp [map_sum, map_smul]
  have hi1 : ∀ j, Integrable (fun z : ι → ℝ ↦ w j • z j • g z) (stdGaussianPi ι) := fun j ↦
    ((integrable_apply_stdGaussianPi j).smul_bdd C₀ hgc.aestronglyMeasurable
      (ae_of_all _ hg0)).smul (w j)
  have hi2 : ∀ j, Integrable (fun z : ι → ℝ ↦ w j • g' z (Pi.single j 1)) (stdGaussianPi ι) :=
    fun j ↦ (Integrable.of_bound (hg'c.clm_apply continuous_const).aestronglyMeasurable
      (C₁ * ‖(Pi.single j 1 : ι → ℝ)‖)
      (ae_of_all _ fun z ↦ (g' z).le_of_opNorm_le (hg1 z) _)).smul (w j)
  simp_rw [hexp, Finset.sum_smul, mul_smul]
  rw [integral_finset_sum _ fun j _ ↦ hi1 j, integral_finset_sum _ fun j _ ↦ hi2 j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_smul, integral_smul,
    integral_apply_smul_eq_integral_hasFDerivAt hg hg'c hg0 hg1 j]

/-- Scalar form of Gaussian integration by parts:
`E[Zᵢ g(Z)] = E[∂ᵢ g(Z)]` for `C¹` functions `g` with `g` and `Dg` bounded. -/
theorem integral_apply_mul_eq_integral_fderiv {g : (ι → ℝ) → ℝ} (hg : ContDiff ℝ 1 g)
    (hb : ∃ C, ∀ z, |g z| ≤ C) (hb' : ∃ C, ∀ z, ‖fderiv ℝ g z‖ ≤ C) (i : ι) :
    ∫ z, z i * g z ∂stdGaussianPi ι = ∫ z, fderiv ℝ g z (Pi.single i 1) ∂stdGaussianPi ι := by
  obtain ⟨C₀, hC₀⟩ := hb
  obtain ⟨C₁, hC₁⟩ := hb'
  have := integral_apply_smul_eq_integral_hasFDerivAt (g' := fderiv ℝ g)
    (fun z ↦ (hg.differentiable le_rfl z).hasFDerivAt) (hg.continuous_fderiv le_rfl)
    (C₀ := C₀) (fun z ↦ by simpa [Real.norm_eq_abs] using hC₀ z) hC₁ i
  simpa [smul_eq_mul] using this

end Coordinate

/-! ## A first-moment bound -/

section Moment

variable {ι : Type*} [Fintype ι]

/-- `E|⟨w, Z⟩| ≤ ‖w‖₂` for a standard Gaussian `Z`. -/
theorem integral_abs_sum_mul_le (w : ι → ℝ) :
    ∫ z, |∑ j, w j * z j| ∂stdGaussianPi ι ≤ √(∑ j, w j ^ 2) := by
  classical
  have hXi : Integrable (fun z : ι → ℝ ↦ ∑ j, w j * z j) (stdGaussianPi ι) :=
    integrable_finset_sum _ fun j _ ↦ (integrable_apply_stdGaussianPi j).const_mul _
  have h : ∀ z : ι → ℝ, (∑ j, w j * z j) ^ 2 = ∑ j, ∑ k, (w j * w k) * (z j * z k) := by
    intro z
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  have hX2i : Integrable (fun z : ι → ℝ ↦ (∑ j, w j * z j) ^ 2) (stdGaussianPi ι) :=
    (integrable_finset_sum _ fun j _ ↦ integrable_finset_sum _ fun k _ ↦
      (integrable_apply_mul_apply_stdGaussianPi j k).const_mul _).congr
      (ae_of_all _ fun z ↦ (h z).symm)
  have hX2 : ∫ z, (∑ j, w j * z j) ^ 2 ∂stdGaussianPi ι = ∑ j, w j ^ 2 := by
    simp_rw [h]
    rw [integral_finset_sum _ fun j _ ↦ integrable_finset_sum _ fun k _ ↦
      (integrable_apply_mul_apply_stdGaussianPi j k).const_mul _]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_finset_sum _ fun k _ ↦
      (integrable_apply_mul_apply_stdGaussianPi j k).const_mul _]
    simp_rw [integral_const_mul, integral_apply_mul_apply_stdGaussianPi]
    simp [sq]
  rcases (Finset.sum_nonneg fun j _ ↦ sq_nonneg (w j) :
      (0 : ℝ) ≤ ∑ j, w j ^ 2).eq_or_lt with h0 | hpos
  · have hw : ∀ j, w j = 0 := fun j ↦ by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (w j))).1 h0.symm j
        (Finset.mem_univ _)
      exact (pow_eq_zero_iff two_ne_zero).1 this
    simp [hw]
  · set c := √(∑ j, w j ^ 2) with hc_def
    have hc : 0 < c := Real.sqrt_pos.2 hpos
    have hc2 : c ^ 2 = ∑ j, w j ^ 2 := Real.sq_sqrt hpos.le
    have hpt : ∀ z : ι → ℝ, |∑ j, w j * z j| ≤ (c ^ 2 + (∑ j, w j * z j) ^ 2) / (2 * c) := by
      intro z
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|∑ j, w j * z j| - c), sq_abs (∑ j, w j * z j)]
    calc ∫ z, |∑ j, w j * z j| ∂stdGaussianPi ι
        ≤ ∫ z, (c ^ 2 + (∑ j, w j * z j) ^ 2) / (2 * c) ∂stdGaussianPi ι :=
          integral_mono hXi.abs (((integrable_const _).add hX2i).div_const _) hpt
      _ = (c ^ 2 + ∑ j, w j ^ 2) / (2 * c) := by
          rw [integral_div, integral_add (integrable_const _) hX2i, hX2]
          simp
      _ = c := by
          rw [← hc2]
          field_simp
          ring

end Moment

/-! ## Gaussian smoothing -/

section Smoothing

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- Gaussian smoothing through a rectangular factor `L`: `x ↦ E φ(x + L Z)`, `Z` standard
Gaussian on `ι' → ℝ`. -/
noncomputable def gaussSmooth (φ : (ι → ℝ) → F) (L : Matrix ι ι' ℝ) (x : ι → ℝ) : F :=
  ∫ z, φ (x + L *ᵥ z) ∂stdGaussianPi ι'

omit [Fintype ι] in
theorem continuous_mulVec_const (L : Matrix ι ι' ℝ) : Continuous (fun z : ι' → ℝ ↦ L *ᵥ z) :=
  continuous_const.matrix_mulVec continuous_id

omit [CompleteSpace F] [Fintype ι] in
theorem norm_gaussSmooth_le {φ : (ι → ℝ) → F} {C : ℝ} (hφ : ∀ y, ‖φ y‖ ≤ C)
    (L : Matrix ι ι' ℝ) (x : ι → ℝ) : ‖gaussSmooth φ L x‖ ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := stdGaussianPi ι')
    (ae_of_all _ fun z ↦ hφ (x + L *ᵥ z))
  simpa [gaussSmooth] using this

omit [CompleteSpace F] in
theorem continuous_gaussSmooth {φ : (ι → ℝ) → F} (hφc : Continuous φ) {C : ℝ}
    (hφ : ∀ y, ‖φ y‖ ≤ C) (L : Matrix ι ι' ℝ) : Continuous (gaussSmooth φ L) :=
  continuous_of_dominated (bound := fun _ ↦ C)
    (fun _ ↦ (hφc.comp (continuous_const.add (continuous_mulVec_const L))).aestronglyMeasurable)
    (fun _ ↦ ae_of_all _ fun _ ↦ hφ _) (integrable_const C)
    (ae_of_all _ fun _ ↦ hφc.comp (continuous_id.add continuous_const))

omit [CompleteSpace F] in
/-- Differentiation under the integral: `D (gaussSmooth φ L) = gaussSmooth (Dφ) L`. -/
theorem hasFDerivAt_gaussSmooth {φ : (ι → ℝ) → F} (hφ : Differentiable ℝ φ)
    (hφ'c : Continuous (fderiv ℝ φ)) {C₀ C₁ : ℝ} (hφ0 : ∀ y, ‖φ y‖ ≤ C₀)
    (hφ1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ C₁) (L : Matrix ι ι' ℝ) (x : ι → ℝ) :
    HasFDerivAt (gaussSmooth φ L) (gaussSmooth (fderiv ℝ φ) L x) x := by
  have hLc := continuous_mulVec_const L
  have hφc := hφ.continuous
  unfold gaussSmooth
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun x z ↦ fderiv ℝ φ (x + L *ᵥ z)) (bound := fun _ ↦ C₁) zero_lt_one ?_ ?_ ?_ ?_
    (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun x' ↦
      (hφc.comp (continuous_const.add hLc)).aestronglyMeasurable
  · exact Integrable.of_bound (hφc.comp (continuous_const.add hLc)).aestronglyMeasurable C₀
      (ae_of_all _ fun z ↦ hφ0 _)
  · exact (hφ'c.comp (continuous_const.add hLc)).aestronglyMeasurable
  · exact ae_of_all _ fun z x' _ ↦ hφ1 _
  · refine ae_of_all _ fun z x' _ ↦ ?_
    have := (hφ (x' + L *ᵥ z)).hasFDerivAt.comp x' ((hasFDerivAt_id x').add_const (L *ᵥ z))
    simpa using this

omit [CompleteSpace F] in
/-- The hypotheses of `hasFDerivAt_gaussSmooth` for `ψ = Dʲφ`, `j < n`. -/
theorem iteratedFDeriv_smooth_props {n : ℕ} {φ : (ι → ℝ) → F} (hφ : ContDiff ℝ n φ)
    (hbd : ∀ j ≤ n, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ C) {j : ℕ} (hj : j < n) :
    Differentiable ℝ (iteratedFDeriv ℝ j φ) ∧ Continuous (fderiv ℝ (iteratedFDeriv ℝ j φ)) ∧
      ∃ C₁, ∀ y, ‖fderiv ℝ (iteratedFDeriv ℝ j φ) y‖ ≤ C₁ := by
  refine ⟨hφ.differentiable_iteratedFDeriv (by exact_mod_cast hj), ?_, ?_⟩
  · rw [fderiv_iteratedFDeriv]
    exact (LinearIsometryEquiv.continuous _).comp
      (hφ.continuous_iteratedFDeriv (m := j + 1) (by exact_mod_cast hj))
  · obtain ⟨C, hC⟩ := hbd (j + 1) hj
    exact ⟨C, fun y ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hC y⟩

theorem integral_linearIsometryEquiv_comm' {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {X : Type*} [MeasurableSpace X] {μ : Measure X} (e : E ≃ₗᵢ[ℝ] G) (φ : X → E) :
    ∫ x, e (φ x) ∂μ = e (∫ x, φ x ∂μ) :=
  e.toLinearIsometry.integral_comp_comm φ

/-- Iterated derivatives commute with Gaussian smoothing. -/
theorem iteratedFDeriv_gaussSmooth {n : ℕ} {φ : (ι → ℝ) → F} (hφ : ContDiff ℝ n φ)
    (hbd : ∀ j ≤ n, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ C) (L : Matrix ι ι' ℝ) :
    ∀ j ≤ n, iteratedFDeriv ℝ j (gaussSmooth φ L) = gaussSmooth (iteratedFDeriv ℝ j φ) L := by
  intro j hj
  induction j with
  | zero =>
    funext x
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp_apply, gaussSmooth]
    rw [integral_linearIsometryEquiv_comm']
  | succ j ih =>
    have hj' : j < n := hj
    obtain ⟨hd, hdc, C₁, hC₁⟩ := iteratedFDeriv_smooth_props hφ hbd hj'
    obtain ⟨C₀, hC₀⟩ := hbd j hj'.le
    funext x
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih hj'.le,
      (hasFDerivAt_gaussSmooth hd hdc hC₀ hC₁ L x).fderiv]
    simp only [gaussSmooth]
    exact (integral_linearIsometryEquiv_comm'
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ ι → ℝ) F).symm
      (fun z ↦ fderiv ℝ (iteratedFDeriv ℝ j φ) (x + L *ᵥ z))).symm

theorem bdd_iteratedFDeriv_gaussSmooth {n : ℕ} {φ : (ι → ℝ) → F} (hφ : ContDiff ℝ n φ)
    (hbd : ∀ j ≤ n, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ C) (L : Matrix ι ι' ℝ) :
    ∀ j ≤ n, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j (gaussSmooth φ L) y‖ ≤ C := by
  intro j hj
  obtain ⟨C, hC⟩ := hbd j hj
  exact ⟨C, fun y ↦ by
    rw [iteratedFDeriv_gaussSmooth hφ hbd L j hj]; exact norm_gaussSmooth_le hC L y⟩

/-- Gaussian smoothing of a `Cⁿ` function with bounded derivatives up to order `n` is `Cⁿ`. -/
theorem contDiff_gaussSmooth {n : ℕ} {φ : (ι → ℝ) → F} (hφ : ContDiff ℝ n φ)
    (hbd : ∀ j ≤ n, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ C) (L : Matrix ι ι' ℝ) :
    ContDiff ℝ n (gaussSmooth φ L) := by
  rw [contDiff_nat_iff_continuous_differentiable]
  refine ⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩
  · rw [iteratedFDeriv_gaussSmooth hφ hbd L m hm]
    obtain ⟨C, hC⟩ := hbd m hm
    exact continuous_gaussSmooth (hφ.continuous_iteratedFDeriv (by exact_mod_cast hm)) hC L
  · rw [iteratedFDeriv_gaussSmooth hφ hbd L m hm.le]
    obtain ⟨hd, hdc, C₁, hC₁⟩ := iteratedFDeriv_smooth_props hφ hbd hm
    obtain ⟨C₀, hC₀⟩ := hbd m hm.le
    exact fun x ↦ (hasFDerivAt_gaussSmooth hd hdc hC₀ hC₁ L x).differentiableAt

omit [CompleteSpace F] [Fintype ι] in
/-- Semigroup splitting: for `a² + b² = 1`,
`E φ(x + L Z) = E_{Z₁} E_{Z₂} φ(x + a L Z₁ + b L Z₂)`. -/
theorem gaussSmooth_eq_gaussSmooth_gaussSmooth {φ : (ι → ℝ) → F} (hφc : Continuous φ) {C : ℝ}
    (hφ : ∀ y, ‖φ y‖ ≤ C) (L : Matrix ι ι' ℝ) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    gaussSmooth φ L = gaussSmooth (gaussSmooth φ (b • L)) (a • L) := by
  funext x
  set Ψ : (ι' → ℝ) → F := fun y ↦ φ (x + L *ᵥ y) with hΨ
  have hΨc : Continuous Ψ := hφc.comp (continuous_const.add (continuous_mulVec_const L))
  have hmap := stdGaussianPi_prod_map_add (ι := ι') a b
  rw [hab, Real.sqrt_one] at hmap
  simp only [one_smul, Measure.map_id'] at hmap
  have hm : Measurable (fun p : (ι' → ℝ) × (ι' → ℝ) ↦ a • p.1 + b • p.2) := by fun_prop
  have h1 : gaussSmooth φ L x = ∫ p, Ψ (a • p.1 + b • p.2)
      ∂((stdGaussianPi ι').prod (stdGaussianPi ι')) := by
    unfold gaussSmooth
    conv_lhs => rw [← hmap]
    exact integral_map hm.aemeasurable hΨc.aestronglyMeasurable
  have hint : Integrable (fun p : (ι' → ℝ) × (ι' → ℝ) ↦ Ψ (a • p.1 + b • p.2))
      ((stdGaussianPi ι').prod (stdGaussianPi ι')) :=
    Integrable.of_bound (hΨc.comp (by fun_prop :
      Continuous fun p : (ι' → ℝ) × (ι' → ℝ) ↦ a • p.1 + b • p.2)).aestronglyMeasurable C
      (ae_of_all _ fun p ↦ hφ _)
  rw [h1, integral_prod _ hint]
  simp only [gaussSmooth]
  congr 1
  funext z₁
  congr 1
  funext z₂
  simp only [Ψ, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.smul_mulVec, add_assoc]

omit [CompleteSpace F] in
/-- One derivative on the Gaussian: if every `h` has a preimage `L w = h` with
`‖w‖₂ ≤ r ‖h‖`, then `‖gaussSmooth (Dψ) L x‖ ≤ r · sup ‖ψ‖`. -/
theorem norm_gaussSmooth_fderiv_le {ψ : (ι → ℝ) → F} (hψ : Differentiable ℝ ψ)
    (hψ'c : Continuous (fderiv ℝ ψ)) {C₀ C₁ : ℝ} (hψ0 : ∀ y, ‖ψ y‖ ≤ C₀)
    (hψ1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ C₁) {L : Matrix ι ι' ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hR : ∀ h : ι → ℝ, ∃ w : ι' → ℝ, L *ᵥ w = h ∧ ∑ j, w j ^ 2 ≤ r ^ 2 * ‖h‖ ^ 2)
    (x : ι → ℝ) : ‖gaussSmooth (fderiv ℝ ψ) L x‖ ≤ r * C₀ := by
  classical
  have hC₀ : 0 ≤ C₀ := (norm_nonneg _).trans (hψ0 0)
  have hLc := continuous_mulVec_const L
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  obtain ⟨w, hLw, hw⟩ := hR h
  set Lc : (ι' → ℝ) →L[ℝ] (ι → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
  set g : (ι' → ℝ) → F := fun z ↦ ψ (x + L *ᵥ z) with hg_def
  set g' : (ι' → ℝ) → (ι' → ℝ) →L[ℝ] F := fun z ↦ (fderiv ℝ ψ (x + L *ᵥ z)).comp Lc
    with hg'_def
  have hg : ∀ z, HasFDerivAt g (g' z) z := fun z ↦
    (hψ (x + L *ᵥ z)).hasFDerivAt.comp z (Lc.hasFDerivAt.const_add x)
  have hg'c : Continuous g' := (hψ'c.comp (continuous_const.add hLc)).clm_comp continuous_const
  have hIBP := integral_sum_mul_smul_eq_integral_hasFDerivAt hg hg'c (C₀ := C₀)
    (C₁ := C₁ * ‖Lc‖) (fun z ↦ hψ0 _)
    (fun z ↦ (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hψ1 _) (norm_nonneg _))) w
  have hint : Integrable (fun z ↦ fderiv ℝ ψ (x + L *ᵥ z)) (stdGaussianPi ι') :=
    Integrable.of_bound (hψ'c.comp (continuous_const.add hLc)).aestronglyMeasurable C₁
      (ae_of_all _ fun z ↦ hψ1 _)
  have hgc : Continuous g := hψ.continuous.comp (continuous_const.add hLc)
  have heq : gaussSmooth (fderiv ℝ ψ) L x h =
      ∫ z, (∑ j, w j * z j) • g z ∂stdGaussianPi ι' := by
    rw [hIBP]
    unfold gaussSmooth
    rw [ContinuousLinearMap.integral_apply hint h, ← hLw]
    rfl
  have hsq : √(∑ j, w j ^ 2) ≤ r * ‖h‖ :=
    (Real.sqrt_le_sqrt hw).trans_eq (by rw [← mul_pow, Real.sqrt_sq (by positivity)])
  rw [heq]
  calc ‖∫ z, (∑ j, w j * z j) • g z ∂stdGaussianPi ι'‖
      ≤ ∫ z, |∑ j, w j * z j| * C₀ ∂stdGaussianPi ι' := by
        refine norm_integral_le_of_norm_le
          ((integrable_finset_sum _ fun j _ ↦
            (integrable_apply_stdGaussianPi j).const_mul _).abs.mul_const _)
          (ae_of_all _ fun z ↦ ?_)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hψ0 _) (abs_nonneg _)
    _ = (∫ z, |∑ j, w j * z j| ∂stdGaussianPi ι') * C₀ := integral_mul_const _ _
    _ ≤ √(∑ j, w j ^ 2) * C₀ := mul_le_mul_of_nonneg_right (integral_abs_sum_mul_le w) hC₀
    _ ≤ (r * ‖h‖) * C₀ := mul_le_mul_of_nonneg_right hsq hC₀
    _ = r * C₀ * ‖h‖ := by ring

/-- The constant in the Gaussian-smoothing derivative bound: `1, √2, 2√2, 8, …`. -/
noncomputable def gaussDerivConst : ℕ → ℝ
  | 0 => 1
  | k + 1 => √2 ^ (k + 1) * gaussDerivConst k

theorem gaussDerivConst_nonneg (k : ℕ) : 0 ≤ gaussDerivConst k := by
  induction k with
  | zero => simp [gaussDerivConst]
  | succ k ih => simp only [gaussDerivConst]; positivity

/-- **Derivative bounds for Gaussian smoothing** (right-inverse form): if every `h : ι → ℝ` has a
preimage `L w = h` with `∑ⱼ wⱼ² ≤ r² ‖h‖²`, then for `φ` of class `Cⁿ` with bounded derivatives
and `‖φ‖ ≤ B`, `‖Dᵏ (gaussSmooth φ L) x‖ ≤ gaussDerivConst k · rᵏ · B` for every `k ≤ n`.
Only `B` enters the bound; the derivative bounds of `φ` are qualitative. -/
theorem norm_iteratedFDeriv_gaussSmooth_le_of_rightInv {n : ℕ} {φ : (ι → ℝ) → F}
    (hφ : ContDiff ℝ n φ) (hbd : ∀ j ≤ n, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ C) {B : ℝ}
    (hB : ∀ y, ‖φ y‖ ≤ B) :
    ∀ k ≤ n, ∀ (L : Matrix ι ι' ℝ) (r : ℝ), 0 ≤ r →
      (∀ h : ι → ℝ, ∃ w : ι' → ℝ, L *ᵥ w = h ∧ ∑ j, w j ^ 2 ≤ r ^ 2 * ‖h‖ ^ 2) →
      ∀ x, ‖iteratedFDeriv ℝ k (gaussSmooth φ L) x‖ ≤ gaussDerivConst k * r ^ k * B := by
  intro k hk
  induction k with
  | zero =>
    intro L r _ _ x
    rw [norm_iteratedFDeriv_zero]
    simpa [gaussDerivConst] using norm_gaussSmooth_le hB L x
  | succ k ih =>
    intro L r hr hR x
    have hk' : k < n := hk
    set a : ℝ := (√2)⁻¹ with ha_def
    have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs2pos : 0 < √2 := by positivity
    have hab : a ^ 2 + a ^ 2 = 1 := by
      rw [ha_def, inv_pow, hs2]; norm_num
    have hRa : ∀ h : ι → ℝ, ∃ w : ι' → ℝ, (a • L) *ᵥ w = h ∧
        ∑ j, w j ^ 2 ≤ (√2 * r) ^ 2 * ‖h‖ ^ 2 := by
      intro h
      obtain ⟨w, hw, hw2⟩ := hR h
      refine ⟨√2 • w, ?_, ?_⟩
      · rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
          show a * √2 = 1 from inv_mul_cancel₀ hs2pos.ne', one_smul, hw]
      · simp only [Pi.smul_apply, smul_eq_mul, mul_pow, hs2]
        rw [← Finset.mul_sum]
        nlinarith [hw2]
    have hr' : 0 ≤ √2 * r := by positivity
    set ψ := gaussSmooth φ (a • L) with hψ_def
    have hψ : ContDiff ℝ n ψ := contDiff_gaussSmooth hφ hbd _
    have hψbd := bdd_iteratedFDeriv_gaussSmooth hφ hbd (a • L)
    have hsplit : gaussSmooth φ L = gaussSmooth ψ (a • L) :=
      gaussSmooth_eq_gaussSmooth_gaussSmooth hφ.continuous hB L hab
    have hIH : ∀ y, ‖iteratedFDeriv ℝ k ψ y‖ ≤ gaussDerivConst k * (√2 * r) ^ k * B :=
      ih hk'.le (a • L) (√2 * r) hr' hRa
    obtain ⟨hd, hdc, C₁, hC₁⟩ := iteratedFDeriv_smooth_props hψ hψbd hk'
    rw [hsplit, ← norm_fderiv_iteratedFDeriv, iteratedFDeriv_gaussSmooth hψ hψbd (a • L) k hk'.le,
      (hasFDerivAt_gaussSmooth hd hdc hIH hC₁ (a • L) x).fderiv]
    refine (norm_gaussSmooth_fderiv_le hd hdc hIH hC₁ hr' hRa x).trans (le_of_eq ?_)
    simp only [gaussDerivConst]
    ring

/-- A positive-definite `L Lᵀ` (in the sense `v ‖u‖² ≤ uᵀ L Lᵀ u`, sup norm) gives a right
inverse of `L` with `∑ⱼ wⱼ² ≤ (|ι| / √v)² ‖h‖²`. -/
theorem exists_mulVec_eq_of_quadForm_ge {L : Matrix ι ι' ℝ} {v : ℝ} (hv0 : 0 < v)
    (hv : ∀ u : ι → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L * Lᵀ) *ᵥ u)) (h : ι → ℝ) :
    ∃ w : ι' → ℝ, L *ᵥ w = h ∧
      ∑ j, w j ^ 2 ≤ ((Fintype.card ι : ℝ) / √v) ^ 2 * ‖h‖ ^ 2 := by
  classical
  have hinj : Function.Injective (L * Lᵀ).mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have ha' : (L * Lᵀ) *ᵥ a = 0 := ha
    have h1 := hv a
    rw [ha', dotProduct_zero] at h1
    have h2 : ‖a‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg a])
  obtain ⟨a, ha⟩ := (LinearMap.injective_iff_surjective.1 hinj) h
  have ha' : (L * Lᵀ) *ᵥ a = h := ha
  refine ⟨Lᵀ *ᵥ a, by rw [Matrix.mulVec_mulVec]; exact ha', ?_⟩
  have hdot : ∑ j, (Lᵀ *ᵥ a) j ^ 2 = a ⬝ᵥ h := by
    have : ∑ j, (Lᵀ *ᵥ a) j ^ 2 = (Lᵀ *ᵥ a) ⬝ᵥ (Lᵀ *ᵥ a) := by simp [dotProduct, sq]
    rw [this, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, ha',
      dotProduct_comm]
  have hD : a ⬝ᵥ h ≤ Fintype.card ι * (‖a‖ * ‖h‖) := by
    unfold dotProduct
    calc ∑ i, a i * h i ≤ ∑ _i : ι, ‖a‖ * ‖h‖ := Finset.sum_le_sum fun i _ ↦
          calc a i * h i ≤ |a i * h i| := le_abs_self _
            _ = |a i| * |h i| := abs_mul _ _
            _ ≤ ‖a‖ * ‖h‖ := mul_le_mul (abs_apply_le_norm a i) (abs_apply_le_norm h i)
                (abs_nonneg _) (norm_nonneg _)
      _ = _ := by simp
  have hq := hv a
  rw [ha'] at hq
  rw [hdot, div_pow, Real.sq_sqrt hv0.le, div_mul_eq_mul_div, le_div_iff₀ hv0]
  set A := ‖a‖
  set H := (Fintype.card ι : ℝ) * ‖h‖
  have hA : 0 ≤ A := norm_nonneg _
  have hH : 0 ≤ H := by positivity
  have hD' : a ⬝ᵥ h ≤ A * H := by rw [show A * H = Fintype.card ι * (A * ‖h‖) by ring]; exact hD
  have hgoal : a ⬝ᵥ h * v ≤ H ^ 2 := by
    rcases hA.eq_or_lt with h0 | hpos
    · rw [← h0] at hD'
      nlinarith
    · have hvA : v * A ≤ H := by
        have : A * (v * A) ≤ A * H := by nlinarith
        exact le_of_mul_le_mul_left this hpos
      nlinarith [mul_le_mul_of_nonneg_left hvA hH]
  calc a ⬝ᵥ h * v ≤ H ^ 2 := hgoal
    _ = (Fintype.card ι : ℝ) ^ 2 * ‖h‖ ^ 2 := by ring

/-- **Derivative bounds for Gaussian smoothing** (quadratic-form version): for `φ` of class `Cⁿ`
with bounded derivatives and `‖φ‖ ≤ B`, and `L` with `v ‖u‖² ≤ uᵀ (L Lᵀ) u` (`v > 0`, sup norm), every
`k ≤ n` satisfies `‖Dᵏ (gaussSmooth φ L) x‖ ≤ gaussDerivConst k · |ι|ᵏ · B · v^{-k/2}`.
The constant depends only on `k` and `|ι|`, not on `ι'`. -/
theorem norm_iteratedFDeriv_gaussSmooth_le {n : ℕ} {φ : (ι → ℝ) → F} (hφ : ContDiff ℝ n φ)
    (hbd : ∀ j ≤ n, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ C) {B : ℝ} (hB : ∀ y, ‖φ y‖ ≤ B)
    {L : Matrix ι ι' ℝ} {v : ℝ} (hv0 : 0 < v)
    (hv : ∀ u : ι → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L * Lᵀ) *ᵥ u)) {k : ℕ} (hk : k ≤ n) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ k (gaussSmooth φ L) x‖ ≤
      gaussDerivConst k * (Fintype.card ι : ℝ) ^ k * B * v ^ (-(k : ℝ) / 2) := by
  have h := norm_iteratedFDeriv_gaussSmooth_le_of_rightInv hφ hbd hB k hk L
    ((Fintype.card ι : ℝ) / √v) (by positivity) (exists_mulVec_eq_of_quadForm_ge hv0 hv) x
  refine h.trans_eq ?_
  have hpow : v ^ (-(k : ℝ) / 2) = ((√v) ^ k)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hv0.le, ← Real.rpow_neg hv0.le]
    ring_nf
  rw [hpow, div_pow]
  ring

/-- **Derivative bounds for plain Gaussian smoothing** `f_s(x) = E φ(x + s Z)`:
`‖Dᵏ f_s x‖ ≤ gaussDerivConst k · √|ι|ᵏ · B / sᵏ` for `k ≤ n`. -/
theorem norm_iteratedFDeriv_gaussSmooth_smul_le {n : ℕ} {φ : (ι → ℝ) → F}
    (hφ : ContDiff ℝ n φ) (hbd : ∀ j ≤ n, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ C) {B : ℝ}
    (hB : ∀ y, ‖φ y‖ ≤ B) {s : ℝ} (hs : 0 < s) {k : ℕ} (hk : k ≤ n) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ k (fun x ↦ ∫ z, φ (x + s • z) ∂stdGaussianPi ι) x‖ ≤
      gaussDerivConst k * √(Fintype.card ι : ℝ) ^ k * B / s ^ k := by
  classical
  have hfun : (fun x ↦ ∫ z, φ (x + s • z) ∂stdGaussianPi ι) =
      gaussSmooth φ (s • (1 : Matrix ι ι ℝ)) := by
    funext x
    simp only [gaussSmooth, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hR : ∀ h : ι → ℝ, ∃ w : ι → ℝ, (s • (1 : Matrix ι ι ℝ)) *ᵥ w = h ∧
      ∑ j, w j ^ 2 ≤ (√(Fintype.card ι : ℝ) / s) ^ 2 * ‖h‖ ^ 2 := by
    intro h
    refine ⟨s⁻¹ • h, ?_, ?_⟩
    · rw [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    · have hsum : ∑ j, h j ^ 2 ≤ (Fintype.card ι : ℝ) * ‖h‖ ^ 2 := by
        calc ∑ j, h j ^ 2 ≤ ∑ _j : ι, ‖h‖ ^ 2 := Finset.sum_le_sum fun j _ ↦ by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (abs_apply_le_norm h j) 2
          _ = _ := by simp
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
      rw [← Finset.mul_sum, div_pow, Real.sq_sqrt (by positivity), inv_pow]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      refine Eq.trans_le ?_ hsum
      field_simp
  rw [hfun]
  refine (norm_iteratedFDeriv_gaussSmooth_le_of_rightInv hφ hbd hB k hk _ _ (by positivity)
    hR x).trans_eq ?_
  rw [div_pow]
  ring

end Smoothing

end StatisticalRL.Probability

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Smooth sandwiches of indicator functions (milestone M2, without the support clause)

Infrastructure for the all-convex-sets route of Theorem 7.11 of arXiv:2610.41903v1
(milestone M2 / G2 of the route plan, as amended by fixes F2, F3 and F5 of the P0 check,
`docs/critic-allconvex-p0.md`).
This file states no source result.

The carrier is `ι → ℝ` for a finite type `ι`, with **Mathlib's default sup norm**
`‖x‖ = sup_i |x i|`; balls, `Metric.thickening` and the operator norms of iterated derivatives
(`iteratedFDeriv`) are all taken with respect to this norm. The measure is `volume` (Lebesgue).

For a set `A` and `δ > 0`, `smoothIndicator A δ = 1_A ⋆ ρ_δ`, where `ρ_δ x = δ^{-d} ρ₁ (δ⁻¹ x)`,
`d = card ι`, and `ρ₁` is a fixed normalised `ContDiffBump` supported in the unit ball. Then
* `smoothIndicator A δ` is `C^∞` (for measurable `A`) with values in `[0,1]`;
* it equals `1` at `x` when the open `δ`-ball around `x` lies in `A`, and `0` when it misses `A`;
* `‖D^k (smoothIndicator A δ) x‖ ≤ δ^{-k} · ∫ ‖D^k ρ₁‖` for every `k` (constant independent of `A`).

The sandwich theorems `exists_smooth_sandwich_upper` (`1_K ≤ φ ≤ 1_{thickening ε K}`) and
`exists_smooth_sandwich_lower` (`1_{K_{-ε}} ≤ φ ≤ 1_K` with `K_{-ε} = {x | closedBall x ε ⊆ K}`) hold
for **every** set `K` (convexity is not needed for this step), with
`‖D^k φ x‖ ≤ sandwichConst ι k / ε ^ k` for all `k : ℕ` (in particular `k = 1, 2, 3`), and with
`sandwichConst ι k = 2^k ∫ ‖D^k ρ₁‖` depending only on `ι` and `k`. The smoothed sets are open
(`thickening`) or closed (complement of a thickening), hence Borel (F3). The derivative-support clause
of the original plan is not provided (F5). The bounds hold for all `k`, and `φ` is `C^∞`, which is
what the integral-form third-order Taylor remainder (F2) consumes.
-/

open MeasureTheory Metric Set Function ContinuousLinearMap Filter
open scoped Convolution

noncomputable section

namespace StatisticalRL.Analysis.ConvexSmoothIndicator

variable (ι : Type*) [Fintype ι]

/-- The fixed bump `ρ₁` before normalisation: radii `1/2 < 1`, centred at `0`. -/
def unitBump : ContDiffBump (0 : ι → ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The fixed normalised mollifier `ρ₁ ≥ 0` with `∫ ρ₁ = 1` and support the open unit ball. -/
def mollifier : (ι → ℝ) → ℝ := (unitBump ι).normed volume

/-- The constant of the derivative bounds: `2^k · ∫ ‖D^k ρ₁‖`. It depends only on `ι` and `k`. -/
def sandwichConst (k : ℕ) : ℝ := 2 ^ k * ∫ x, ‖iteratedFDeriv ℝ k (mollifier ι) x‖

variable {ι}

theorem mollifier_nonneg (x : ι → ℝ) : 0 ≤ mollifier ι x := (unitBump ι).nonneg_normed x

theorem contDiff_mollifier (n : ℕ) : ContDiff ℝ n (mollifier ι) :=
  contDiff_infty.1 ((unitBump ι).contDiff_normed (n := ⊤)) n

theorem integral_mollifier : ∫ x, mollifier ι x = 1 := (unitBump ι).integral_normed

theorem support_mollifier : support (mollifier ι) = ball (0 : ι → ℝ) 1 :=
  (unitBump ι).support_normed_eq

theorem hasCompactSupport_mollifier : HasCompactSupport (mollifier ι) :=
  (unitBump ι).hasCompactSupport_normed

theorem integrable_norm_iteratedFDeriv_mollifier (k : ℕ) :
    Integrable (fun x => ‖iteratedFDeriv ℝ k (mollifier ι) x‖) := by
  have hc : Continuous fun x => iteratedFDeriv ℝ k (mollifier ι) x :=
    (contDiff_mollifier k).continuous_iteratedFDeriv'
  exact (hc.integrable_of_hasCompactSupport (μ := volume)
    (hasCompactSupport_mollifier.iteratedFDeriv k)).norm

theorem sandwichConst_nonneg (k : ℕ) : 0 ≤ sandwichConst ι k :=
  mul_nonneg (pow_nonneg (by norm_num) _) (integral_nonneg fun _ => norm_nonneg _)

/-- Sanity check of the constant: for `k = 0` it is `∫ ρ₁ = 1`. -/
theorem sandwichConst_zero : sandwichConst ι 0 = 1 := by
  simp only [sandwichConst, pow_zero, one_mul, norm_iteratedFDeriv_zero]
  rw [← integral_mollifier (ι := ι)]
  congr 1
  funext x
  exact Real.norm_of_nonneg (mollifier_nonneg x)

/-! ### The scaled mollifier `ρ_δ` -/

/-- `ρ_δ x = δ^{-d} ρ₁ (δ⁻¹ • x)` with `d = card ι`. -/
def scaledMollifier (δ : ℝ) (x : ι → ℝ) : ℝ :=
  (δ ^ Fintype.card ι)⁻¹ * mollifier ι (δ⁻¹ • x)

theorem scaledMollifier_eq (δ : ℝ) :
    scaledMollifier (ι := ι) δ =
      (δ ^ Fintype.card ι)⁻¹ • (mollifier ι ∘ ⇑(δ⁻¹ • ContinuousLinearMap.id ℝ (ι → ℝ))) := by
  funext x
  simp [scaledMollifier, smul_eq_mul]

theorem scaledMollifier_nonneg {δ : ℝ} (hδ : 0 < δ) (x : ι → ℝ) : 0 ≤ scaledMollifier δ x :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hδ.le _)) (mollifier_nonneg _)

theorem contDiff_scaledMollifier (δ : ℝ) (n : ℕ) : ContDiff ℝ n (scaledMollifier (ι := ι) δ) :=
  contDiff_const.mul ((contDiff_mollifier n).comp (contDiff_const_smul δ⁻¹))

theorem scaledMollifier_eq_zero {δ : ℝ} (hδ : 0 < δ) {x : ι → ℝ} (hx : δ ≤ ‖x‖) :
    scaledMollifier δ x = 0 := by
  have h : mollifier ι (δ⁻¹ • x) = 0 := by
    rw [← Function.notMem_support, support_mollifier, mem_ball_zero_iff, not_lt, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
    rw [le_inv_mul_iff₀ hδ, mul_one]
    exact hx
  simp [scaledMollifier, h]

theorem hasCompactSupport_scaledMollifier {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (scaledMollifier (ι := ι) δ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℝ) δ) fun x hx => ?_
  rw [mem_closedBall_zero_iff, not_le] at hx
  exact scaledMollifier_eq_zero hδ hx.le

theorem integral_scaledMollifier {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, scaledMollifier (ι := ι) δ x = 1 := by
  simp only [scaledMollifier]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (mollifier ι) hδ.le,
    Module.finrank_fintype_fun_eq_card, integral_mollifier, smul_eq_mul, mul_one,
    inv_mul_cancel₀ (pow_ne_zero _ hδ.ne')]

theorem integrable_scaledMollifier {δ : ℝ} (hδ : 0 < δ) :
    Integrable (scaledMollifier (ι := ι) δ) :=
  (contDiff_scaledMollifier δ 0).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_scaledMollifier hδ)

theorem norm_iteratedFDeriv_scaledMollifier_le {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ k (scaledMollifier δ) x‖ ≤
      (δ ^ Fintype.card ι)⁻¹ * (δ⁻¹ ^ k * ‖iteratedFDeriv ℝ k (mollifier ι) (δ⁻¹ • x)‖) := by
  set g : (ι → ℝ) →L[ℝ] (ι → ℝ) := δ⁻¹ • ContinuousLinearMap.id ℝ (ι → ℝ) with hg
  have hcomp : ContDiff ℝ k (mollifier ι ∘ ⇑g) := (contDiff_mollifier k).comp g.contDiff
  rw [scaledMollifier_eq, iteratedFDeriv_const_smul_apply hcomp.contDiffAt,
    g.iteratedFDeriv_comp_right (contDiff_mollifier k) x le_rfl, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg hδ.le _))]
  gcongr
  have hgx : g x = δ⁻¹ • x := by simp [hg]
  have hgn : ‖g‖ ≤ δ⁻¹ := by
    rw [hg, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
    exact mul_le_of_le_one_right (inv_nonneg.2 hδ.le) (norm_id_le)
  calc ‖(iteratedFDeriv ℝ k (mollifier ι) (g x)).compContinuousLinearMap fun _ => g‖
      ≤ ‖iteratedFDeriv ℝ k (mollifier ι) (g x)‖ * ∏ _i : Fin k, ‖g‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ k (mollifier ι) (g x)‖ * δ⁻¹ ^ k := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        gcongr
    _ = δ⁻¹ ^ k * ‖iteratedFDeriv ℝ k (mollifier ι) (δ⁻¹ • x)‖ := by rw [hgx, mul_comm]

theorem integrable_norm_iteratedFDeriv_scaledMollifier {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    Integrable (fun x => ‖iteratedFDeriv ℝ k (scaledMollifier (ι := ι) δ) x‖) := by
  have hc : Continuous fun x => iteratedFDeriv ℝ k (scaledMollifier (ι := ι) δ) x :=
    (contDiff_scaledMollifier δ k).continuous_iteratedFDeriv'
  have hs : HasCompactSupport (iteratedFDeriv ℝ k (scaledMollifier (ι := ι) δ)) :=
    (hasCompactSupport_scaledMollifier hδ).iteratedFDeriv k
  exact (hc.integrable_of_hasCompactSupport (μ := volume) hs).norm

/-- Scaling: `∫ ‖D^k ρ_δ‖ ≤ δ^{-k} ∫ ‖D^k ρ₁‖`. -/
theorem integral_norm_iteratedFDeriv_scaledMollifier_le {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∫ x, ‖iteratedFDeriv ℝ k (scaledMollifier (ι := ι) δ) x‖ ≤
      δ⁻¹ ^ k * ∫ x, ‖iteratedFDeriv ℝ k (mollifier ι) x‖ := by
  have hint : Integrable fun x : ι → ℝ =>
      (δ ^ Fintype.card ι)⁻¹ * (δ⁻¹ ^ k * ‖iteratedFDeriv ℝ k (mollifier ι) (δ⁻¹ • x)‖) :=
    (((integrable_norm_iteratedFDeriv_mollifier k).comp_smul
      (inv_ne_zero hδ.ne')).const_mul _).const_mul _
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint
    (Eventually.of_forall fun x => norm_iteratedFDeriv_scaledMollifier_le hδ k x)).trans_eq ?_
  rw [integral_const_mul, integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume
      (fun y => ‖iteratedFDeriv ℝ k (mollifier ι) y‖) hδ.le,
    Module.finrank_fintype_fun_eq_card, smul_eq_mul, ← mul_assoc, ← mul_assoc, mul_comm _ (δ⁻¹ ^ k),
    mul_assoc, mul_assoc, ← mul_assoc (δ ^ Fintype.card ι)⁻¹,
    inv_mul_cancel₀ (pow_ne_zero _ hδ.ne'), one_mul]

/-! ### Iterated derivatives of a convolution with a smooth compactly supported kernel -/

section Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_linearIsometryEquiv_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F] (e : E ≃ₗᵢ[ℝ] F) (φ : (ι → ℝ) → E) :
    ∫ x, e (φ x) = e (∫ x, φ x) :=
  e.toLinearIsometry.integral_comp_comm φ

theorem fderiv_lsmul_convolution {f : (ι → ℝ) → ℝ} {g : (ι → ℝ) → E}
    (hf : LocallyIntegrable f volume) (hcg : HasCompactSupport g) (hg : ContDiff ℝ 1 g) :
    fderiv ℝ (f ⋆[lsmul ℝ ℝ, volume] g) = f ⋆[lsmul ℝ ℝ, volume] fderiv ℝ g := by
  funext x
  rw [(hcg.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf hg x).fderiv]
  simp only [convolution_def]
  congr 1

theorem iteratedFDeriv_lsmul_convolution {f : (ι → ℝ) → ℝ} {g : (ι → ℝ) → ℝ}
    (hf : LocallyIntegrable f volume) (hcg : HasCompactSupport g) (hg : ∀ n : ℕ, ContDiff ℝ n g)
    (k : ℕ) :
    iteratedFDeriv ℝ k (f ⋆[lsmul ℝ ℝ, volume] g) =
      f ⋆[lsmul ℝ ℝ, volume] iteratedFDeriv ℝ k g := by
  induction k with
  | zero =>
    funext x
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, convolution_lsmul]
    rw [← integral_linearIsometryEquiv_comm]
    simp only [LinearIsometryEquiv.map_smul]
  | succ k ih =>
    have hck : HasCompactSupport (iteratedFDeriv ℝ k g) := hcg.iteratedFDeriv k
    have hdk : ContDiff ℝ 1 (iteratedFDeriv ℝ k g) :=
      (hg (1 + k)).iteratedFDeriv_right (by push_cast; exact le_rfl)
    rw [iteratedFDeriv_succ_eq_comp_left, ih, fderiv_lsmul_convolution hf hck hdk,
      iteratedFDeriv_succ_eq_comp_left (f := g)]
    funext x
    simp only [Function.comp_apply, convolution_lsmul]
    refine (integral_linearIsometryEquiv_comm _
      (fun t => f t • fderiv ℝ (iteratedFDeriv ℝ k g) (x - t))).symm.trans ?_
    congr 1

end Convolution

/-! ### The smoothed indicator -/

/-- `smoothIndicator A δ = 1_A ⋆ ρ_δ`. -/
def smoothIndicator (A : Set (ι → ℝ)) (δ : ℝ) : (ι → ℝ) → ℝ :=
  A.indicator (fun _ => (1 : ℝ)) ⋆[lsmul ℝ ℝ, volume] scaledMollifier δ

theorem smoothIndicator_apply (A : Set (ι → ℝ)) (δ : ℝ) (x : ι → ℝ) :
    smoothIndicator A δ x = ∫ t, A.indicator (fun _ => (1 : ℝ)) (x - t) * scaledMollifier δ t := by
  rw [smoothIndicator, convolution_lsmul_swap]
  rfl

theorem smoothIndicator_mem_Icc (A : Set (ι → ℝ)) {δ : ℝ} (hδ : 0 < δ) (x : ι → ℝ) :
    smoothIndicator A δ x ∈ Icc (0 : ℝ) 1 := by
  have h0 : ∀ t, 0 ≤ A.indicator (fun _ => (1 : ℝ)) (x - t) * scaledMollifier δ t := fun t =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (scaledMollifier_nonneg hδ t)
  rw [smoothIndicator_apply]
  refine ⟨integral_nonneg h0, ?_⟩
  refine (integral_mono_of_nonneg (Eventually.of_forall h0) (integrable_scaledMollifier hδ)
    (Eventually.of_forall fun t => ?_)).trans_eq (integral_scaledMollifier hδ)
  refine mul_le_of_le_one_left (scaledMollifier_nonneg hδ t) ?_
  exact Set.indicator_le_self' (fun _ _ => zero_le_one) _

theorem smoothIndicator_eq_one (A : Set (ι → ℝ)) {δ : ℝ} (hδ : 0 < δ) {x : ι → ℝ}
    (hx : ∀ t : ι → ℝ, ‖t‖ < δ → x - t ∈ A) : smoothIndicator A δ x = 1 := by
  rw [smoothIndicator_apply]
  refine (integral_congr_ae (Eventually.of_forall fun t => ?_)).trans (integral_scaledMollifier hδ)
  by_cases ht : ‖t‖ < δ
  · simp [Set.indicator_of_mem (hx t ht)]
  · simp [scaledMollifier_eq_zero hδ (not_lt.1 ht)]

theorem smoothIndicator_eq_zero (A : Set (ι → ℝ)) {δ : ℝ} (hδ : 0 < δ) {x : ι → ℝ}
    (hx : ∀ t : ι → ℝ, ‖t‖ < δ → x - t ∉ A) : smoothIndicator A δ x = 0 := by
  rw [smoothIndicator_apply]
  refine (integral_congr_ae (Eventually.of_forall fun t => ?_)).trans (integral_zero _ _)
  by_cases ht : ‖t‖ < δ
  · simp [Set.indicator_of_notMem (hx t ht)]
  · simp [scaledMollifier_eq_zero hδ (not_lt.1 ht)]

theorem contDiff_smoothIndicator {A : Set (ι → ℝ)} (hA : MeasurableSet A) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (smoothIndicator A δ) := by
  have hloc : LocallyIntegrable (A.indicator fun _ => (1 : ℝ)) volume :=
    (locallyIntegrable_const 1).indicator hA
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scaledMollifier (ι := ι) δ) :=
    contDiff_infty.2 (contDiff_scaledMollifier δ)
  exact (hasCompactSupport_scaledMollifier hδ).contDiff_convolution_right (lsmul ℝ ℝ) hloc hsm

/-- `‖(f ⋆ G) x‖ ≤ ∫ ‖G‖` when `|f| ≤ 1`. -/
theorem norm_lsmul_convolution_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℝ) → ℝ} (hf : ∀ t, ‖f t‖ ≤ 1) {G : (ι → ℝ) → E}
    (hG : Integrable fun t => ‖G t‖) (x : ι → ℝ) :
    ‖(f ⋆[lsmul ℝ ℝ, volume] G) x‖ ≤ ∫ t, ‖G t‖ := by
  rw [convolution_lsmul]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_sub_left_eq_self (fun t => ‖G t‖) volume x]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (hG.comp_sub_left x) (Eventually.of_forall fun t => ?_)
  show ‖f t • G (x - t)‖ ≤ ‖G (x - t)‖
  rw [norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hf t)

/-- Derivative bound: `‖D^k (1_A ⋆ ρ_δ) x‖ ≤ ∫ ‖D^k ρ_δ‖`. -/
theorem norm_iteratedFDeriv_smoothIndicator_le' {A : Set (ι → ℝ)} (hA : MeasurableSet A) {δ : ℝ}
    (hδ : 0 < δ) (k : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ k (smoothIndicator A δ) x‖ ≤
      ∫ t, ‖iteratedFDeriv ℝ k (scaledMollifier (ι := ι) δ) t‖ := by
  have hloc : LocallyIntegrable (A.indicator fun _ => (1 : ℝ)) volume :=
    (locallyIntegrable_const 1).indicator hA
  have hint := integrable_norm_iteratedFDeriv_scaledMollifier (ι := ι) hδ k
  have hf : ∀ t, ‖A.indicator (fun _ => (1 : ℝ)) t‖ ≤ 1 := fun t => by
    by_cases ht : t ∈ A <;> simp [ht]
  have heq := iteratedFDeriv_lsmul_convolution hloc (hasCompactSupport_scaledMollifier hδ)
    (contDiff_scaledMollifier δ) k
  unfold smoothIndicator
  rw [heq]
  exact norm_lsmul_convolution_le hf hint x

/-- Derivative bound with the explicit constant: `‖D^k (1_A ⋆ ρ_δ) x‖ ≤ δ^{-k} ∫ ‖D^k ρ₁‖`. -/
theorem norm_iteratedFDeriv_smoothIndicator_le {A : Set (ι → ℝ)} (hA : MeasurableSet A) {δ : ℝ}
    (hδ : 0 < δ) (k : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ k (smoothIndicator A δ) x‖ ≤
      δ⁻¹ ^ k * ∫ t, ‖iteratedFDeriv ℝ k (mollifier ι) t‖ :=
  (norm_iteratedFDeriv_smoothIndicator_le' hA hδ k x).trans
    (integral_norm_iteratedFDeriv_scaledMollifier_le hδ k)

theorem norm_iteratedFDeriv_smoothIndicator_half_le {A : Set (ι → ℝ)} (hA : MeasurableSet A)
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ k (smoothIndicator A (ε / 2)) x‖ ≤ sandwichConst ι k / ε ^ k := by
  refine (norm_iteratedFDeriv_smoothIndicator_le hA (half_pos hε) k x).trans_eq ?_
  rw [sandwichConst, inv_div, div_pow]
  ring

/-! ### The sandwiches -/

/-- **Upper smooth sandwich.** For every set `K ⊆ ι → ℝ` (sup norm) and `ε > 0` there is a `C^∞`
function `φ` with values in `[0,1]`, `φ = 1` on `K`, `φ = 0` off the open `ε`-thickening of `K`, and
`‖D^k φ x‖ ≤ sandwichConst ι k / ε ^ k` for every `k` and `x`. The witness is
`smoothIndicator (thickening (ε/2) K) (ε/2)`. Convexity of `K` is not needed. -/
theorem exists_smooth_sandwich_upper (K : Set (ι → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : (ι → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ (∀ x, φ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ K, φ x = 1) ∧ (∀ x ∉ thickening ε K, φ x = 0) ∧
      ∀ (k : ℕ) (x : ι → ℝ), ‖iteratedFDeriv ℝ k φ x‖ ≤ sandwichConst ι k / ε ^ k := by
  have hε2 : 0 < ε / 2 := half_pos hε
  have hA : MeasurableSet (thickening (ε / 2) K) := isOpen_thickening.measurableSet
  refine ⟨smoothIndicator (thickening (ε / 2) K) (ε / 2), contDiff_smoothIndicator hA hε2,
    smoothIndicator_mem_Icc _ hε2, fun x hx => ?_, fun x hx => ?_,
    norm_iteratedFDeriv_smoothIndicator_half_le hA hε⟩
  · refine smoothIndicator_eq_one _ hε2 fun t ht => ?_
    rw [mem_thickening_iff]
    exact ⟨x, hx, by rwa [dist_eq_norm, sub_sub_cancel_left, norm_neg]⟩
  · refine smoothIndicator_eq_zero _ hε2 fun t ht hmem => hx ?_
    obtain ⟨z, hz, hdz⟩ := mem_thickening_iff.1 hmem
    refine mem_thickening_iff.2 ⟨z, hz, ?_⟩
    calc dist x z ≤ dist x (x - t) + dist (x - t) z := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add_of_le_of_lt ?_ hdz
          rw [dist_eq_norm, sub_sub_cancel]
          exact ht.le
      _ = ε := add_halves ε

/-- **Lower smooth sandwich.** For every set `K ⊆ ι → ℝ` (sup norm) and `ε > 0` there is a `C^∞`
function `φ` with values in `[0,1]`, `φ x = 1` whenever `closedBall x ε ⊆ K`, `φ = 0` off `K`, and
`‖D^k φ x‖ ≤ sandwichConst ι k / ε ^ k` for every `k` and `x`. The witness is
`smoothIndicator (thickening (ε/2) Kᶜ)ᶜ (ε/2)`. Convexity of `K` is not needed. -/
theorem exists_smooth_sandwich_lower (K : Set (ι → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : (ι → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ (∀ x, φ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, closedBall x ε ⊆ K → φ x = 1) ∧ (∀ x ∉ K, φ x = 0) ∧
      ∀ (k : ℕ) (x : ι → ℝ), ‖iteratedFDeriv ℝ k φ x‖ ≤ sandwichConst ι k / ε ^ k := by
  have hε2 : 0 < ε / 2 := half_pos hε
  have hA : MeasurableSet (thickening (ε / 2) Kᶜ)ᶜ := isOpen_thickening.measurableSet.compl
  refine ⟨smoothIndicator (thickening (ε / 2) Kᶜ)ᶜ (ε / 2), contDiff_smoothIndicator hA hε2,
    smoothIndicator_mem_Icc _ hε2, fun x hx => ?_, fun x hx => ?_,
    norm_iteratedFDeriv_smoothIndicator_half_le hA hε⟩
  · refine smoothIndicator_eq_one _ hε2 fun t ht hmem => ?_
    obtain ⟨z, hz, hdz⟩ := mem_thickening_iff.1 hmem
    refine hz (hx ?_)
    rw [mem_closedBall]
    calc dist z x ≤ dist z (x - t) + dist (x - t) x := dist_triangle _ _ _
      _ ≤ ε / 2 + ε / 2 := by
          refine add_le_add ?_ ?_
          · rw [dist_comm]; exact hdz.le
          · rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact ht.le
      _ = ε := add_halves ε
  · refine smoothIndicator_eq_zero _ hε2 fun t ht hmem => hmem ?_
    rw [mem_thickening_iff]
    exact ⟨x, hx, by rwa [dist_eq_norm, sub_sub_cancel_left, norm_neg]⟩

/-- Non-vacuity: on `Fin 1 → ℝ`, the upper sandwich of `{0}` at scale `1` equals `1` at `0` and `0`
at the point `2`, so it is not constant. -/
example : ∃ φ : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ φ 0 = 1 ∧
    φ (fun _ => 2) = 0 ∧
    ∀ (k : ℕ) (x : Fin 1 → ℝ), ‖iteratedFDeriv ℝ k φ x‖ ≤ sandwichConst (Fin 1) k / 1 ^ k := by
  obtain ⟨φ, h1, -, h3, h4, h5⟩ := exists_smooth_sandwich_upper ({0} : Set (Fin 1 → ℝ)) one_pos
  refine ⟨φ, h1, h3 0 rfl, h4 _ ?_, h5⟩
  rw [mem_thickening_iff]
  rintro ⟨z, rfl, hz⟩
  rw [dist_zero_right] at hz
  have : ‖(fun _ => (2 : ℝ) : Fin 1 → ℝ)‖ = 2 := by simp [Pi.norm_def]
  linarith

/-! ### Addendum (critic note N1): the inner parallel set and measurability of the witnesses -/

/-- The inner parallel set `{x | closedBall x ε ⊆ K}` of a convex set is convex. -/
theorem convex_setOf_closedBall_subset {K : Set (ι → ℝ)} (hK : Convex ℝ K) (ε : ℝ) :
    Convex ℝ {x | closedBall x ε ⊆ K} := by
  intro x hx y hy a b ha hb hab z hz
  have hz' : z = a • (x + (z - (a • x + b • y))) + b • (y + (z - (a • x + b • y))) := by
    rw [smul_add, smul_add]
    have : a • (z - (a • x + b • y)) + b • (z - (a • x + b • y)) = z - (a • x + b • y) := by
      rw [← add_smul, hab, one_smul]
    rw [show a • x + a • (z - (a • x + b • y)) + (b • y + b • (z - (a • x + b • y))) =
      (a • x + b • y) + (a • (z - (a • x + b • y)) + b • (z - (a • x + b • y))) by abel, this]
    abel
  rw [hz']
  have hd : ‖z - (a • x + b • y)‖ ≤ ε := by rw [← dist_eq_norm]; exact mem_closedBall.1 hz
  refine hK (hx ?_) (hy ?_) ha hb hab
  · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hd
  · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hd

/-- The inner parallel set `{x | closedBall x ε ⊆ K}` of a closed set is closed (hence Borel). -/
theorem isClosed_setOf_closedBall_subset {K : Set (ι → ℝ)} (hK : IsClosed K) (ε : ℝ) :
    IsClosed {x | closedBall x ε ⊆ K} := by
  have : {x | closedBall x ε ⊆ K} = ⋂ t ∈ closedBall (0 : ι → ℝ) ε, (fun x => x + t) ⁻¹' K := by
    ext x; simp only [mem_setOf_eq, mem_iInter, mem_preimage]
    constructor
    · intro h t ht; apply h; rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      simpa using ht
    · intro h y hy; have := h (y - x) (by simpa [dist_eq_norm] using hy); simpa using this
  rw [this]
  exact isClosed_biInter fun t _ => hK.preimage (continuous_id.add continuous_const)

/-- The inner parallel set of a closed set is measurable. -/
theorem measurableSet_setOf_closedBall_subset {K : Set (ι → ℝ)} (hK : IsClosed K) (ε : ℝ) :
    MeasurableSet {x | closedBall x ε ⊆ K} :=
  (isClosed_setOf_closedBall_subset hK ε).measurableSet

/-- Any `C^∞` function on `ι → ℝ`, in particular each sandwich witness of
`exists_smooth_sandwich_upper` and `exists_smooth_sandwich_lower`, is measurable. -/
theorem measurable_of_contDiff_top {φ : (ι → ℝ) → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) : Measurable φ :=
  hφ.continuous.measurable

/-- The smoothed indicator of a measurable set is measurable. -/
theorem measurable_smoothIndicator {A : Set (ι → ℝ)} (hA : MeasurableSet A) {δ : ℝ} (hδ : 0 < δ) :
    Measurable (smoothIndicator A δ) :=
  measurable_of_contDiff_top (contDiff_smoothIndicator hA hδ)

end StatisticalRL.Analysis.ConvexSmoothIndicator

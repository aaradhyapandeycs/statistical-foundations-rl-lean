import Formalization.Probability.GaussianCovCompare
import Formalization.Probability.GaussianIBP
import Formalization.Probability.ConvexSandwichShell
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Order.Chebyshev

/-!
# Gaussian-vs-Gaussian comparison on convex sets, linear in the covariance difference

Infrastructure (milestone M4.2 of the all-convex route to Theorem 7.11,
`thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`). Nothing here is a source result.

Main export `abs_real_convex_gaussian_sub_le`: if `Σᵢ = Lᵢ Lᵢᵀ` satisfy
`v ‖u‖² ≤ uᵀ Σᵢ u` (sup norm, `v > 0`), then for every convex `K ⊆ ι → ℝ` (measurable or not;
`.real` is the outer measure)
`|N(0,Σ₁)(K) − N(0,Σ₂)(K)| ≤ gaussCmpConst ι / v · entryMax (Σ₁ − Σ₂)`,
with `N(0,Σᵢ)` the image of `stdGaussianPi` under `Lᵢ`.

Proof (no `t`-derivative, no `√`-rate):
* reservoir: with `r = v / (|ι| + 1)`, `Σᵢ − r I ⪰ 0`, so `N(Σᵢ) = N(Σᵢ − rI) ⋆ N(rI)` and
  `E φ(Yᵢ) = E h(Pᵢ Z)` with `h = gaussSmooth φ (√r I)`, `Pᵢ Pᵢᵀ = Σᵢ − rI`
  (law identity M4.1 + `measurePreserving_sumPiEquivProdPi`);
* `‖D²h‖ ≤ gaussDerivConst 2 · |ι| / r` uses only `sup |φ| ≤ 1` (M3);
* common upper covariance: with `δ = Σ₁ − Σ₂`, `c = |ι| · entryMax δ`, both `D₁ = cI − δ` and
  `D₂ = cI` are PSD and `Σ₁ − rI + D₁ = Σ₂ − rI + D₂`;
* second-order Taylor + `E W = 0`: `|E h(y + W) − h(y)| ≤ sup‖D²h‖ · tr Cov W`, so
  `|E h(Pᵢ Z) − E h(Pᵢ Z + Qᵢ Z')| ≤ sup‖D²h‖ · tr Dᵢ`;
* the smooth upper sandwich of `interior K` (M2) and the shell bound (M1) give the indicator
  version up to `O(ε)`; let `ε → 0`.
-/

open MeasureTheory ProbabilityTheory Real Metric Set Matrix
open scoped Matrix

namespace StatisticalRL.Probability

open StatisticalRL.Analysis.ConvexSmoothIndicator

section Defs

variable {ι : Type*} [Fintype ι]

/-- Largest absolute entry of a square matrix (`0` for the empty index type). -/
noncomputable def entryMax (A : Matrix ι ι ℝ) : ℝ := ⨆ p : ι × ι, |A p.1 p.2|

theorem abs_le_entryMax (A : Matrix ι ι ℝ) (i j : ι) : |A i j| ≤ entryMax A :=
  le_ciSup (f := fun p : ι × ι ↦ |A p.1 p.2|) (Set.finite_range _).bddAbove (i, j)

omit [Fintype ι] in
theorem entryMax_nonneg (A : Matrix ι ι ℝ) : 0 ≤ entryMax A :=
  Real.iSup_nonneg fun _ ↦ abs_nonneg _

omit [Fintype ι] in
theorem entryMax_zero : entryMax (0 : Matrix ι ι ℝ) = 0 := by
  simp [entryMax]

variable (ι) in
/-- The constant of the Gaussian–Gaussian convex comparison:
`gaussDerivConst 2 · |ι| (|ι| + 1) (2|ι|² + |ι|)`. -/
noncomputable def gaussCmpConst : ℝ :=
  gaussDerivConst 2 * Fintype.card ι * (Fintype.card ι + 1) *
    (2 * (Fintype.card ι : ℝ) ^ 2 + Fintype.card ι)

theorem gaussCmpConst_nonneg : 0 ≤ gaussCmpConst ι := by
  have := gaussDerivConst_nonneg 2
  unfold gaussCmpConst; positivity

end Defs

namespace GaussianConvexCompare

variable {ι κ₁ κ₂ : Type*} [Fintype ι] [Fintype κ₁] [Fintype κ₂]

/-! ### Elementary norm and quadratic-form bounds -/

theorem norm_sq_le_sum_mul_self (w : ι → ℝ) : ‖w‖ ^ 2 ≤ ∑ i, w i * w i := by
  have hS : 0 ≤ ∑ i, w i * w i := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have h : ‖w‖ ≤ √(∑ i, w i * w i) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i ↦ ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    rw [sq]
    exact Finset.single_le_sum (f := fun j ↦ w j * w j) (fun j _ ↦ mul_self_nonneg _)
      (Finset.mem_univ i)
  calc ‖w‖ ^ 2 ≤ (√(∑ i, w i * w i)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS

theorem sum_mul_self_le_card_mul_norm_sq (u : ι → ℝ) :
    ∑ i, u i * u i ≤ Fintype.card ι * ‖u‖ ^ 2 := by
  calc ∑ i, u i * u i ≤ ∑ _i : ι, ‖u‖ ^ 2 := Finset.sum_le_sum fun i _ ↦ by
        rw [← sq, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_apply_le_norm u i) 2
    _ = _ := by simp

theorem dotProduct_mulVec_le_entryMax (δ : Matrix ι ι ℝ) (u : ι → ℝ) :
    u ⬝ᵥ (δ *ᵥ u) ≤ Fintype.card ι * entryMax δ * ∑ i, u i * u i := by
  set m := entryMax δ
  have hm : 0 ≤ m := entryMax_nonneg δ
  have h1 : u ⬝ᵥ (δ *ᵥ u) ≤ ∑ i, ∑ j, m * (|u i| * |u j|) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
    calc u i * (δ i j * u j) ≤ |u i * (δ i j * u j)| := le_abs_self _
      _ = |δ i j| * (|u i| * |u j|) := by rw [abs_mul, abs_mul]; ring
      _ ≤ m * (|u i| * |u j|) :=
          mul_le_mul_of_nonneg_right (abs_le_entryMax δ i j) (by positivity)
  have h2 : ∑ i, ∑ j, m * (|u i| * |u j|) = m * (∑ i, |u i|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ by rw [Finset.mul_sum]
  have h3 : (∑ i, |u i|) ^ 2 ≤ Fintype.card ι * ∑ i, u i * u i := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ |u i|)
    simpa [sq_abs, ← sq] using this
  calc u ⬝ᵥ (δ *ᵥ u) ≤ m * (∑ i, |u i|) ^ 2 := h1.trans_eq h2
    _ ≤ m * (Fintype.card ι * ∑ i, u i * u i) := mul_le_mul_of_nonneg_left h3 hm
    _ = _ := by ring

omit [Fintype ι] in
theorem isHermitian_of_transpose_eq {A : Matrix ι ι ℝ} (h : Aᵀ = A) : A.IsHermitian := by
  show Aᴴ = A
  rw [conjTranspose_eq_transpose_of_trivial, h]

theorem posSemidef_of_dotProduct {A : Matrix ι ι ℝ} (h : Aᵀ = A)
    (hq : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)) : A.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_of_transpose_eq h)
    fun x ↦ by rw [star_trivial]; exact hq x

omit [Fintype ι] in
theorem transpose_mul_transpose_self {κ : Type*} [Fintype κ] (L : Matrix ι κ ℝ) :
    (L * Lᵀ)ᵀ = L * Lᵀ := by
  rw [transpose_mul, transpose_transpose]

/-! ### Law identities -/

omit [Fintype ι] in
theorem fromCols_mul_transpose (P : Matrix ι κ₁ ℝ) (Q : Matrix ι κ₂ ℝ) :
    fromCols P Q * (fromCols P Q)ᵀ = P * Pᵀ + Q * Qᵀ := by
  rw [transpose_fromCols, fromCols_mul_fromRows]

/-- Integrating a bounded continuous function against the image of `stdGaussianPi (κ₁ ⊕ κ₂)`
under `[P | Q]` is integrating `f (P z₁ + Q z₂)` over two independent standard Gaussians. -/
theorem integral_map_fromCols_mulVec {f : (ι → ℝ) → ℝ} (hf : Continuous f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) (P : Matrix ι κ₁ ℝ) (Q : Matrix ι κ₂ ℝ) :
    ∫ x, f x ∂((stdGaussianPi (κ₁ ⊕ κ₂)).map (fromCols P Q *ᵥ ·)) =
      ∫ z₁, ∫ z₂, f (P *ᵥ z₁ + Q *ᵥ z₂) ∂stdGaussianPi κ₂ ∂stdGaussianPi κ₁ := by
  rw [integral_map (measurable_mulVec _).aemeasurable hf.aestronglyMeasurable]
  have hmp := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : κ₁ ⊕ κ₂ ↦ ℝ)
    (fun _ ↦ gaussianReal 0 1)
  have h1 : ∫ w, f (fromCols P Q *ᵥ w) ∂stdGaussianPi (κ₁ ⊕ κ₂) =
      ∫ p, f (P *ᵥ p.1 + Q *ᵥ p.2) ∂((stdGaussianPi κ₁).prod (stdGaussianPi κ₂)) := by
    rw [← hmp.integral_comp']
    refine integral_congr_ae (ae_of_all _ fun p ↦ ?_)
    show f (fromCols P Q *ᵥ _) = _
    rw [fromCols_mulVec]
    rfl
  have hint : Integrable (fun p : (κ₁ → ℝ) × (κ₂ → ℝ) ↦ f (P *ᵥ p.1 + Q *ᵥ p.2))
      ((stdGaussianPi κ₁).prod (stdGaussianPi κ₂)) :=
    Integrable.of_bound (hf.comp (by fun_prop)).aestronglyMeasurable B
      (ae_of_all _ fun p ↦ by simpa [Real.norm_eq_abs] using hB _)
  rw [h1, integral_prod _ hint]

/-! ### Second-order Taylor bound and the Gaussian perturbation bound -/

/-- Second-order Taylor remainder: `|h(y+w) − h(y) − Dh(y) w| ≤ M ‖w‖²` when
`‖D²h‖ ≤ M` everywhere. -/
theorem abs_sub_sub_fderiv_le {h : (ι → ℝ) → ℝ} (hh : ContDiff ℝ 2 h) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ M) (y w : ι → ℝ) :
    |h (y + w) - h y - fderiv ℝ h y w| ≤ M * ‖w‖ ^ 2 := by
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hd' : Differentiable ℝ (fderiv ℝ h) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hfd2 : ∀ x, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M := by
    intro x
    have h1 := norm_iteratedFDerivWithin_one (𝕜 := ℝ) (fderiv ℝ h)
      (uniqueDiffWithinAt_univ (x := x))
    rw [iteratedFDerivWithin_univ, fderivWithin_univ, norm_iteratedFDeriv_fderiv] at h1
    rw [← h1]; exact hM x
  have hlip : ∀ a b, ‖fderiv ℝ h a - fderiv ℝ h b‖ ≤ M * ‖a - b‖ := fun a b ↦
    convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fderiv ℝ h)
      (fun x _ ↦ (hd' x).hasFDerivAt.hasFDerivWithinAt) (fun x _ ↦ hfd2 x) (mem_univ b)
      (mem_univ a)
  set g : (ι → ℝ) → ℝ := fun x ↦ h (y + x) - fderiv ℝ h y x with hg_def
  have hg : ∀ x, HasFDerivAt g (fderiv ℝ h (y + x) - fderiv ℝ h y) x := by
    intro x
    have h1 : HasFDerivAt (fun x ↦ h (y + x)) (fderiv ℝ h (y + x)) x := by
      simpa using (hd (y + x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_add y)
    exact h1.sub (fderiv ℝ h y).hasFDerivAt
  have hbound : ∀ x ∈ closedBall (0 : ι → ℝ) ‖w‖,
      ‖fderiv ℝ h (y + x) - fderiv ℝ h y‖ ≤ M * ‖w‖ := by
    intro x hx
    refine (hlip _ _).trans ?_
    rw [add_sub_cancel_left]
    exact mul_le_mul_of_nonneg_left (by simpa using hx) hM0
  have hw : w ∈ closedBall (0 : ι → ℝ) ‖w‖ := by simp
  have key := (convex_closedBall (0 : ι → ℝ) ‖w‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ ↦ (hg x).hasFDerivWithinAt) hbound (mem_closedBall_self (norm_nonneg w)) hw
  simp only [hg_def, add_zero, map_zero, sub_zero, Real.norm_eq_abs] at key
  have e : h (y + w) - h y - fderiv ℝ h y w = h (y + w) - fderiv ℝ h y w - h y := by ring
  rw [e]
  exact key.trans_eq (by ring)

theorem integrable_mulVec_apply (Q : Matrix ι ι ℝ) (i : ι) :
    Integrable (fun z ↦ (Q *ᵥ z) i) (stdGaussianPi ι) := by
  simp only [Matrix.mulVec, dotProduct]
  exact integrable_finset_sum _ fun k _ ↦ (integrable_apply_stdGaussianPi k).const_mul _

theorem integrable_mulVec_apply_mul_self (Q : Matrix ι ι ℝ) (i : ι) :
    Integrable (fun z ↦ (Q *ᵥ z) i * (Q *ᵥ z) i) (stdGaussianPi ι) := by
  have e : ∀ z : ι → ℝ, (Q *ᵥ z) i * (Q *ᵥ z) i = ∑ k, ∑ l, Q i k * Q i l * (z k * z l) := by
    intro z
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
  exact (integrable_finset_sum _ fun k _ ↦ integrable_finset_sum _ fun l _ ↦
    (integrable_apply_mul_apply_stdGaussianPi k l).const_mul _).congr
    (ae_of_all _ fun z ↦ (e z).symm)

/-- **Gaussian perturbation bound.** For `h` of class `C²` with `|h| ≤ B` and `‖D²h‖ ≤ M`,
`|E h(y + Q Z) − h(y)| ≤ M · tr(Q Qᵀ)`: the first-order term vanishes since `E Z = 0`. -/
theorem abs_gaussSmooth_sub_le {h : (ι → ℝ) → ℝ} (hh : ContDiff ℝ 2 h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ M)
    (Q : Matrix ι ι ℝ) (y : ι → ℝ) :
    |gaussSmooth h Q y - h y| ≤ M * ∑ i, (Q * Qᵀ) i i := by
  classical
  set ℓ := fderiv ℝ h y with hℓ
  have hc : Continuous h := hh.continuous
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hQc := continuous_mulVec_const Q
  have hI1 : Integrable (fun z ↦ h (y + Q *ᵥ z)) (stdGaussianPi ι) :=
    Integrable.of_bound (hc.comp (continuous_const.add hQc)).aestronglyMeasurable B
      (ae_of_all _ fun z ↦ by simpa [Real.norm_eq_abs] using hB _)
  have hexp : ∀ w : ι → ℝ, ℓ w = ∑ i, w i * ℓ (Pi.single i 1) := by
    intro w
    have hw : w = ∑ j, w j • (Pi.single j (1 : ℝ) : ι → ℝ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hw]
    simp [map_sum, map_smul]
  have hfun : (fun z ↦ ℓ (Q *ᵥ z)) = fun z ↦ ∑ i, (Q *ᵥ z) i * ℓ (Pi.single i 1) :=
    funext fun z ↦ hexp _
  have hI2 : Integrable (fun z ↦ ℓ (Q *ᵥ z)) (stdGaussianPi ι) := by
    rw [hfun]
    exact integrable_finset_sum _ fun i _ ↦ (integrable_mulVec_apply Q i).mul_const _
  have hlin : ∫ z, ℓ (Q *ᵥ z) ∂stdGaussianPi ι = 0 := by
    rw [hfun, integral_finset_sum _ fun i _ ↦ (integrable_mulVec_apply Q i).mul_const _]
    simp [integral_mul_const, integral_mulVec_apply_stdGaussianPi]
  have hsqsum : Integrable (fun z ↦ M * ∑ i, (Q *ᵥ z) i * (Q *ᵥ z) i) (stdGaussianPi ι) :=
    (integrable_finset_sum _ fun i _ ↦ integrable_mulVec_apply_mul_self Q i).const_mul M
  have hint_sq : ∫ z, M * ∑ i, (Q *ᵥ z) i * (Q *ᵥ z) i ∂stdGaussianPi ι =
      M * ∑ i, (Q * Qᵀ) i i := by
    rw [integral_const_mul, integral_finset_sum _ fun i _ ↦ integrable_mulVec_apply_mul_self Q i]
    simp_rw [integral_mulVec_apply_mul_mulVec_apply_stdGaussianPi]
  have key : gaussSmooth h Q y - h y =
      ∫ z, (h (y + Q *ᵥ z) - h y - ℓ (Q *ᵥ z)) ∂stdGaussianPi ι := by
    rw [integral_sub (f := fun z ↦ h (y + Q *ᵥ z) - h y) (hI1.sub (integrable_const _)) hI2,
      hlin, sub_zero, integral_sub hI1 (integrable_const (h y)), integral_const]
    simp [gaussSmooth]
  rw [key, ← Real.norm_eq_abs, ← hint_sq]
  refine norm_integral_le_of_norm_le hsqsum (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_eq_abs]
  exact (abs_sub_sub_fderiv_le hh hM y _).trans
    (mul_le_mul_of_nonneg_left (norm_sq_le_sum_mul_self _) hM0)

/-! ### PSD bookkeeping -/

theorem posSemidef_gram_sub_reservoir [DecidableEq ι] {κ : Type*} [Fintype κ] (L : Matrix ι κ ℝ) {v : ℝ}
    (hv : 0 < v) (h : ∀ u : ι → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L * Lᵀ) *ᵥ u)) :
    (L * Lᵀ - (v / (Fintype.card ι + 1)) • (1 : Matrix ι ι ℝ)).PosSemidef := by
  refine posSemidef_of_dotProduct (by
    rw [transpose_sub, transpose_smul, transpose_one, transpose_mul_transpose_self]) fun x ↦ ?_
  rw [sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have h1 := h x
  have h2 : x ⬝ᵥ x ≤ n * ‖x‖ ^ 2 := sum_mul_self_le_card_mul_norm_sq x
  have h3 : v / (n + 1) * (x ⬝ᵥ x) ≤ v * ‖x‖ ^ 2 := by
    calc v / (n + 1) * (x ⬝ᵥ x) ≤ v / (n + 1) * (n * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ v * ‖x‖ ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg hv.le (sq_nonneg ‖x‖)]
  linarith

theorem posSemidef_smul_one_sub [DecidableEq ι] (δ : Matrix ι ι ℝ) (hδ : δᵀ = δ) :
    ((Fintype.card ι * entryMax δ) • (1 : Matrix ι ι ℝ) - δ).PosSemidef := by
  refine posSemidef_of_dotProduct (by rw [transpose_sub, transpose_smul, transpose_one, hδ])
    fun x ↦ ?_
  rw [sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  have := dotProduct_mulVec_le_entryMax δ x
  have e : x ⬝ᵥ x = ∑ i, x i * x i := rfl
  rw [e]
  linarith

theorem posSemidef_smul_one [DecidableEq ι] {c : ℝ} (hc : 0 ≤ c) : (c • (1 : Matrix ι ι ℝ)).PosSemidef := by
  refine posSemidef_of_dotProduct (by rw [transpose_smul, transpose_one]) fun x ↦ ?_
  rw [Matrix.smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  exact mul_nonneg hc (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)

/-! ### The smooth comparison -/

/-- Second-derivative bound for the reservoir smoothing `gaussSmooth φ (√r I)`: only `sup |φ|`
enters. -/
theorem norm_iteratedFDeriv_two_reservoir_le [DecidableEq ι] {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hbd : ∀ j ≤ 2, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ C) (hB : ∀ y, ‖φ y‖ ≤ 1) {r : ℝ}
    (hr : 0 < r) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ 2 (gaussSmooth φ (√r • (1 : Matrix ι ι ℝ))) x‖ ≤
      gaussDerivConst 2 * Fintype.card ι / r := by
  have hfun : gaussSmooth φ (√r • (1 : Matrix ι ι ℝ)) =
      fun x ↦ ∫ z, φ (x + √r • z) ∂stdGaussianPi ι := by
    funext x
    simp only [gaussSmooth, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hfun]
  refine (norm_iteratedFDeriv_gaussSmooth_smul_le hφ hbd hB (Real.sqrt_pos.2 hr) le_rfl
    x).trans_eq ?_
  rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hr.le]
  ring

/-- One side of the comparison: if `L Lᵀ = P Pᵀ + s² I` then `E φ(L Z)` and
`E h([P | Q] Z')`, `h = gaussSmooth φ (s I)`, differ by at most `M · tr(Q Qᵀ)`. -/
theorem abs_integral_map_sub_integral_fromCols_le [DecidableEq ι] {κ : Type*} [Fintype κ] (L : Matrix ι κ ℝ)
    (P Q : Matrix ι ι ℝ) {s : ℝ} (hL : L * Lᵀ = P * Pᵀ + (s * s) • (1 : Matrix ι ι ℝ))
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hbd : ∀ j ≤ 2, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ C) (hB : ∀ y, ‖φ y‖ ≤ 1) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ 2 (gaussSmooth φ (s • (1 : Matrix ι ι ℝ))) x‖ ≤ M) :
    |∫ x, φ x ∂((stdGaussianPi κ).map (L *ᵥ ·)) -
        ∫ x, gaussSmooth φ (s • (1 : Matrix ι ι ℝ)) x
          ∂((stdGaussianPi (ι ⊕ ι)).map (fromCols P Q *ᵥ ·))| ≤
      M * ∑ i, (Q * Qᵀ) i i := by
  set h := gaussSmooth φ (s • (1 : Matrix ι ι ℝ)) with hh_def
  have hφc := hφ.continuous
  have hφB : ∀ y, |φ y| ≤ 1 := fun y ↦ by simpa [Real.norm_eq_abs] using hB y
  have hh : ContDiff ℝ 2 h := contDiff_gaussSmooth hφ hbd _
  have hhB : ∀ x, ‖h x‖ ≤ 1 := norm_gaussSmooth_le hB _
  have hhB' : ∀ x, |h x| ≤ 1 := fun x ↦ by simpa [Real.norm_eq_abs] using hhB x
  have hhc : Continuous h := hh.continuous
  have hlaw : (stdGaussianPi κ).map (L *ᵥ ·) =
      (stdGaussianPi (ι ⊕ ι)).map (fromCols P (s • (1 : Matrix ι ι ℝ)) *ᵥ ·) := by
    refine map_mulVec_stdGaussianPi_eq _ _ ?_
    rw [fromCols_mul_transpose, hL, transpose_smul, transpose_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, smul_smul]
  rw [hlaw, integral_map_fromCols_mulVec hφc hφB, integral_map_fromCols_mulVec hhc hhB']
  change |∫ z₁, h (P *ᵥ z₁) ∂stdGaussianPi ι -
      ∫ z₁, gaussSmooth h Q (P *ᵥ z₁) ∂stdGaussianPi ι| ≤ _
  have hPc := continuous_mulVec_const P
  have hi1 : Integrable (fun z₁ ↦ h (P *ᵥ z₁)) (stdGaussianPi ι) :=
    Integrable.of_bound (hhc.comp hPc).aestronglyMeasurable 1 (ae_of_all _ fun z ↦ hhB _)
  have hi2 : Integrable (fun z₁ ↦ gaussSmooth h Q (P *ᵥ z₁)) (stdGaussianPi ι) :=
    Integrable.of_bound ((continuous_gaussSmooth hhc hhB Q).comp hPc).aestronglyMeasurable 1
      (ae_of_all _ fun z ↦ norm_gaussSmooth_le hhB Q _)
  rw [← integral_sub hi1 hi2, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := stdGaussianPi ι)
    (f := fun z₁ ↦ h (P *ᵥ z₁) - gaussSmooth h Q (P *ᵥ z₁)) (C := M * ∑ i, (Q * Qᵀ) i i)
    (ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact abs_gaussSmooth_sub_le hh hhB' hM Q _)
  simpa using this

/-- **Smooth Gaussian–Gaussian comparison, linear in the covariance difference.** For `φ` of
class `C²` with bounded derivatives and `|φ| ≤ 1`, and `Σᵢ = Lᵢ Lᵢᵀ ⪰ v` (sup norm),
`|E φ(L₁ Z₁) − E φ(L₂ Z₂)| ≤ gaussCmpConst ι / v · entryMax (Σ₁ − Σ₂)`. -/
theorem abs_integral_map_sub_le_of_contDiff (L₁ : Matrix ι κ₁ ℝ) (L₂ : Matrix ι κ₂ ℝ) {v : ℝ}
    (hv : 0 < v) (h₁ : ∀ u : ι → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L₁ * L₁ᵀ) *ᵥ u))
    (h₂ : ∀ u : ι → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L₂ * L₂ᵀ) *ᵥ u)) {φ : (ι → ℝ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hbd : ∀ j ≤ 2, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ C)
    (hB : ∀ y, ‖φ y‖ ≤ 1) :
    |∫ x, φ x ∂((stdGaussianPi κ₁).map (L₁ *ᵥ ·)) -
        ∫ x, φ x ∂((stdGaussianPi κ₂).map (L₂ *ᵥ ·))| ≤
      gaussCmpConst ι / v * entryMax (L₁ * L₁ᵀ - L₂ * L₂ᵀ) := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hn : 0 ≤ n := Nat.cast_nonneg _
  set r := v / (n + 1) with hr_def
  have hr : 0 < r := by positivity
  set s := √r with hs_def
  have hss : s * s = r := Real.mul_self_sqrt hr.le
  set δ := L₁ * L₁ᵀ - L₂ * L₂ᵀ with hδ_def
  set m := entryMax δ with hm_def
  have hm : 0 ≤ m := entryMax_nonneg δ
  set c := n * m with hc_def
  have hc : 0 ≤ c := by positivity
  obtain ⟨P₁, hP₁⟩ := exists_mul_transpose_eq_of_posSemidef (posSemidef_gram_sub_reservoir L₁ hv h₁)
  obtain ⟨P₂, hP₂⟩ := exists_mul_transpose_eq_of_posSemidef (posSemidef_gram_sub_reservoir L₂ hv h₂)
  have hδT : δᵀ = δ := by
    rw [hδ_def, transpose_sub, transpose_mul_transpose_self, transpose_mul_transpose_self]
  obtain ⟨Q₁, hQ₁⟩ := exists_mul_transpose_eq_of_posSemidef (posSemidef_smul_one_sub δ hδT)
  obtain ⟨Q₂, hQ₂⟩ := exists_mul_transpose_eq_of_posSemidef (posSemidef_smul_one (ι := ι) hc)
  set M := gaussDerivConst 2 * n / r with hM_def
  have hM0 : 0 ≤ M := by have := gaussDerivConst_nonneg 2; positivity
  have hM : ∀ x, ‖iteratedFDeriv ℝ 2 (gaussSmooth φ (s • (1 : Matrix ι ι ℝ))) x‖ ≤ M :=
    fun x ↦ norm_iteratedFDeriv_two_reservoir_le hφ hbd hB hr x
  have hL₁ : L₁ * L₁ᵀ = P₁ * P₁ᵀ + (s * s) • (1 : Matrix ι ι ℝ) := by
    rw [hP₁, hss, sub_add_cancel]
  have hL₂ : L₂ * L₂ᵀ = P₂ * P₂ᵀ + (s * s) • (1 : Matrix ι ι ℝ) := by
    rw [hP₂, hss, sub_add_cancel]
  have e1 := abs_integral_map_sub_integral_fromCols_le L₁ P₁ Q₁ hL₁ hφ hbd hB hM
  have e2 := abs_integral_map_sub_integral_fromCols_le L₂ P₂ Q₂ hL₂ hφ hbd hB hM
  have hlaw : (stdGaussianPi (ι ⊕ ι)).map (fromCols P₁ Q₁ *ᵥ ·) =
      (stdGaussianPi (ι ⊕ ι)).map (fromCols P₂ Q₂ *ᵥ ·) := by
    refine map_mulVec_stdGaussianPi_eq _ _ ?_
    rw [fromCols_mul_transpose, fromCols_mul_transpose, hP₁, hP₂, hQ₁, hQ₂, hδ_def]
    abel
  rw [hlaw] at e1
  have htr1 : ∑ i, (Q₁ * Q₁ᵀ) i i ≤ n * (c + m) := by
    rw [hQ₁]
    calc ∑ i, ((c • (1 : Matrix ι ι ℝ) - δ) i i) ≤ ∑ _i : ι, (c + m) :=
          Finset.sum_le_sum fun i _ ↦ by
            simp only [sub_apply, smul_apply, one_apply_eq, smul_eq_mul, mul_one]
            linarith [neg_abs_le (δ i i), abs_le_entryMax δ i i]
      _ = n * (c + m) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have htr2 : ∑ i, (Q₂ * Q₂ᵀ) i i = n * c := by
    rw [hQ₂]
    simp only [smul_apply, one_apply_eq, smul_eq_mul, mul_one, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rfl
  calc _ ≤ M * ∑ i, (Q₁ * Q₁ᵀ) i i + M * ∑ i, (Q₂ * Q₂ᵀ) i i :=
        (abs_sub_le _ _ _).trans (add_le_add e1 (by rw [abs_sub_comm]; exact e2))
    _ ≤ M * (n * (c + m)) + M * (n * c) :=
        add_le_add (mul_le_mul_of_nonneg_left htr1 hM0) (mul_le_mul_of_nonneg_left htr2.le hM0)
    _ = gaussCmpConst ι / v * m := by
        rw [hM_def, hr_def, hc_def, gaussCmpConst, ← hn_def]
        field_simp
        ring

/-! ### From smooth functions to convex sets -/

/-- A Gaussian law `L Z` with `L Lᵀ ⪰ v > 0` is the law of `R Z'` for a square invertible `R`. -/
theorem exists_square_factor_isUnit [DecidableEq ι] {κ : Type*} [Fintype κ] (L : Matrix ι κ ℝ) {v : ℝ}
    (hv : 0 < v) (h : ∀ u : ι → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L * Lᵀ) *ᵥ u)) :
    ∃ R : Matrix ι ι ℝ, IsUnit R.det ∧
      (stdGaussianPi κ).map (L *ᵥ ·) = (stdGaussianPi ι).map (R *ᵥ ·) := by
  classical
  have hpsd : (L * Lᵀ).PosSemidef := posSemidef_of_dotProduct (transpose_mul_transpose_self L)
    fun x ↦ (by positivity : 0 ≤ v * ‖x‖ ^ 2).trans (h x)
  obtain ⟨R, hR⟩ := exists_mul_transpose_eq_of_posSemidef hpsd
  refine ⟨R, ?_, map_mulVec_stdGaussianPi_eq L R hR.symm⟩
  have hinj : Function.Injective (L * Lᵀ).mulVec := by
    intro a b hab
    have h1 := h (a - b)
    rw [mulVec_sub, hab, sub_self, dotProduct_zero] at h1
    have h2 : ‖a - b‖ ^ 2 ≤ 0 := le_of_mul_le_mul_left (by simpa using h1) hv
    exact sub_eq_zero.1 (norm_eq_zero.1
      ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm h2 (sq_nonneg _))))
  have hu : IsUnit (L * Lᵀ) := mulVec_injective_iff_isUnit.1 hinj
  rw [isUnit_iff_isUnit_det, ← hR, det_mul, det_transpose] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- Upper smooth sandwich of `interior K` against an invertible Gaussian image: the integral
lies between the mass of `K` and the mass of `K` plus the M1 shell bound at scale `ε`. -/
theorem real_le_integral_le_add_shell [DecidableEq ι] (R : Matrix ι ι ℝ) (hR : IsUnit R.det)
    {K : Set (ι → ℝ)} (hK : Convex ℝ K) {ε : ℝ} (hε : 0 < ε) {φ : (ι → ℝ) → ℝ}
    (hφc : Continuous φ) (h01 : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (h1 : ∀ x ∈ interior K, φ x = 1)
    (h0 : ∀ x ∉ thickening ε (interior K), φ x = 0) :
    ((stdGaussianPi ι).map (R *ᵥ ·)).real K ≤ ∫ x, φ x ∂((stdGaussianPi ι).map (R *ᵥ ·)) ∧
      ∫ x, φ x ∂((stdGaussianPi ι).map (R *ᵥ ·)) ≤ ((stdGaussianPi ι).map (R *ᵥ ·)).real K +
        4 * (Fintype.card ι : ℝ) ^ 2 * matrixMaxRowAbsSum R⁻¹ * ε / √(2 * π) := by
  set μ := (stdGaussianPi ι).map (R *ᵥ ·) with hμ
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (measurable_mulVec R).aemeasurable
  set U := interior K with hU_def
  have hU : IsOpen U := isOpen_interior
  have hKU : μ.real K = μ.real U := map_mulVec_real_convex_eq_interior R hR hK
  have hφi : Integrable φ μ := Integrable.of_bound hφc.aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (h01 x).1]; exact (h01 x).2)
  have hthm : MeasurableSet (thickening ε U) := isOpen_thickening.measurableSet
  have lo : μ.real U ≤ ∫ x, φ x ∂μ := by
    rw [← integral_indicator_one hU.measurableSet]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hU.measurableSet) hφi
      fun x ↦ ?_
    by_cases hx : x ∈ U
    · simp [hx, h1 x hx]
    · simp [hx, (h01 x).1]
  have hi : ∫ x, φ x ∂μ ≤ μ.real (thickening ε U) := by
    rw [← integral_indicator_one hthm]
    refine integral_mono hφi ((integrable_const (1 : ℝ)).indicator hthm) fun x ↦ ?_
    by_cases hx : x ∈ thickening ε U
    · simp [hx, (h01 x).2]
    · simp [hx, h0 x hx]
  have hsplit : μ.real (thickening ε U) ≤
      μ.real U + μ.real (cthickening ε U ∩ cthickening ε (interior U)ᶜ) := by
    calc μ.real (thickening ε U) ≤
          μ.real (U ∪ (cthickening ε U ∩ cthickening ε (interior U)ᶜ)) :=
          measureReal_mono fun x hx ↦ by
            by_cases hxU : x ∈ U
            · exact Or.inl hxU
            · exact Or.inr (ConvexSandwichShell.thickening_diff_subset_convexShell U hε.le
                ⟨hx, hxU⟩)
      _ ≤ _ := measureReal_union_le _ _
  have hshell := map_mulVec_convexShell_le R hR hK.interior hε.le
  rw [hKU]
  exact ⟨lo, hi.trans (hsplit.trans (by linarith))⟩

end GaussianConvexCompare

open GaussianConvexCompare

variable {ι κ₁ κ₂ : Type*} [Fintype ι] [Fintype κ₁] [Fintype κ₂]

/-- **M4.2: Gaussian–Gaussian comparison on convex sets, linear in the covariance difference**
(infrastructure, not a source result). Let `Σᵢ = Lᵢ Lᵢᵀ` with `v ‖u‖² ≤ uᵀ Σᵢ u` for all `u`
(sup norm, `v > 0`). Then for every convex `K ⊆ ι → ℝ` (not assumed measurable),
`|N(0,Σ₁)(K) − N(0,Σ₂)(K)| ≤ gaussCmpConst ι / v · entryMax (Σ₁ − Σ₂)`, where `N(0,Σᵢ)` is the
image of the standard Gaussian under `Lᵢ`. -/
theorem abs_real_convex_gaussian_sub_le (L₁ : Matrix ι κ₁ ℝ) (L₂ : Matrix ι κ₂ ℝ) {v : ℝ}
    (hv : 0 < v) (h₁ : ∀ u : ι → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L₁ * L₁ᵀ) *ᵥ u))
    (h₂ : ∀ u : ι → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L₂ * L₂ᵀ) *ᵥ u)) {K : Set (ι → ℝ)}
    (hK : Convex ℝ K) :
    |((stdGaussianPi κ₁).map (L₁ *ᵥ ·)).real K - ((stdGaussianPi κ₂).map (L₂ *ᵥ ·)).real K| ≤
      gaussCmpConst ι / v * entryMax (L₁ * L₁ᵀ - L₂ * L₂ᵀ) := by
  classical
  obtain ⟨R₁, hR₁, e₁⟩ := exists_square_factor_isUnit L₁ hv h₁
  obtain ⟨R₂, hR₂, e₂⟩ := exists_square_factor_isUnit L₂ hv h₂
  set A := gaussCmpConst ι / v * entryMax (L₁ * L₁ᵀ - L₂ * L₂ᵀ) with hA
  set C₁ := 4 * (Fintype.card ι : ℝ) ^ 2 * matrixMaxRowAbsSum R₁⁻¹ / √(2 * π) with hC₁_def
  set C₂ := 4 * (Fintype.card ι : ℝ) ^ 2 * matrixMaxRowAbsSum R₂⁻¹ / √(2 * π) with hC₂_def
  have hC₁ : 0 ≤ C₁ := by have := matrixMaxRowAbsSum_nonneg R₁⁻¹; positivity
  have hC₂ : 0 ≤ C₂ := by have := matrixMaxRowAbsSum_nonneg R₂⁻¹; positivity
  have key : ∀ ε, 0 < ε →
      |((stdGaussianPi κ₁).map (L₁ *ᵥ ·)).real K - ((stdGaussianPi κ₂).map (L₂ *ᵥ ·)).real K| ≤
        A + (C₁ + C₂) * ε := by
    intro ε hε
    obtain ⟨φ, hφ, h01, h1, h0, hder⟩ :=
      StatisticalRL.Analysis.ConvexSmoothIndicator.exists_smooth_sandwich_upper (interior K) hε
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (le_trans (by exact_mod_cast le_rfl : (2 : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞))
      (WithTop.coe_le_coe.2 le_top))
    have hbd : ∀ j ≤ 2, ∃ C, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ C := fun j _ ↦ ⟨_, hder j⟩
    have hB : ∀ y, ‖φ y‖ ≤ 1 := fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (h01 y).1]; exact (h01 y).2
    have hcmp := abs_integral_map_sub_le_of_contDiff L₁ L₂ hv h₁ h₂ hφ2 hbd hB
    rw [e₁, e₂] at hcmp ⊢
    obtain ⟨l1, u1⟩ := real_le_integral_le_add_shell R₁ hR₁ hK hε hφ.continuous h01 h1 h0
    obtain ⟨l2, u2⟩ := real_le_integral_le_add_shell R₂ hR₂ hK hε hφ.continuous h01 h1 h0
    have u1' := u1.trans_eq (show _ = _ + C₁ * ε by rw [hC₁_def]; ring)
    have u2' := u2.trans_eq (show _ = _ + C₂ * ε by rw [hC₂_def]; ring)
    rw [abs_le] at hcmp ⊢
    constructor <;> nlinarith [hcmp.1, hcmp.2]
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  have hpos : 0 < C₁ + C₂ + 1 := by positivity
  refine (key (η / (C₁ + C₂ + 1)) (by positivity)).trans ?_
  have : (C₁ + C₂) * (η / (C₁ + C₂ + 1)) ≤ η := by
    rw [mul_div_assoc', div_le_iff₀ hpos]
    nlinarith
  linarith

/-! ### Corollary for `gaussCov` -/

section GaussCov

open StatisticalRL.Ch7Rest.TDInference

variable {State : Type} [Fintype State] [DecidableEq State]

/-- **M4.2 for `gaussCov`** (infrastructure). For `Γ₁, Γ₂ ≥ 0` with covariances
`Σᵢ = A⁻¹ diag(Γᵢ) A⁻ᵀ ⪰ v > 0` (sup norm) and convex `K`,
`|gaussCov A Γ₁ (K) − gaussCov A Γ₂ (K)| ≤ gaussCmpConst State / v · entryMax (Σ₁ − Σ₂)`. -/
theorem abs_real_convex_gaussCov_sub_le (A : Matrix State State ℝ) {Γ₁ Γ₂ : State → ℝ}
    (hΓ₁ : ∀ s, 0 ≤ Γ₁ s) (hΓ₂ : ∀ s, 0 ≤ Γ₂ s) {v : ℝ} (hv : 0 < v)
    (h₁ : ∀ u : State → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((A⁻¹ * diagonal Γ₁ * (A⁻¹)ᵀ) *ᵥ u))
    (h₂ : ∀ u : State → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((A⁻¹ * diagonal Γ₂ * (A⁻¹)ᵀ) *ᵥ u))
    {K : Set (State → ℝ)} (hK : Convex ℝ K) :
    |(gaussCov A Γ₁).real K - (gaussCov A Γ₂).real K| ≤
      gaussCmpConst State / v *
        entryMax (A⁻¹ * diagonal Γ₁ * (A⁻¹)ᵀ - A⁻¹ * diagonal Γ₂ * (A⁻¹)ᵀ) := by
  rw [gaussCov_eq_map_mulVec, gaussCov_eq_map_mulVec, ← gaussCovFactor_mul_transpose A hΓ₁,
    ← gaussCovFactor_mul_transpose A hΓ₂]
  rw [← gaussCovFactor_mul_transpose A hΓ₁] at h₁
  rw [← gaussCovFactor_mul_transpose A hΓ₂] at h₂
  exact abs_real_convex_gaussian_sub_le _ _ hv h₁ h₂ hK

end GaussCov

/-! ### Non-vacuity -/

/-- Equal covariances (possibly different factor shapes): the bound is `0`. -/
example (L₁ : Matrix ι κ₁ ℝ) (L₂ : Matrix ι κ₂ ℝ) (hEq : L₁ * L₁ᵀ = L₂ * L₂ᵀ) {v : ℝ}
    (hv : 0 < v) (h : ∀ u : ι → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L₂ * L₂ᵀ) *ᵥ u)) {K : Set (ι → ℝ)}
    (hK : Convex ℝ K) :
    |((stdGaussianPi κ₁).map (L₁ *ᵥ ·)).real K - ((stdGaussianPi κ₂).map (L₂ *ᵥ ·)).real K| ≤
      0 := by
  have := abs_real_convex_gaussian_sub_le L₁ L₂ hv (hEq ▸ h) h hK
  rwa [hEq, sub_self, entryMax_zero, mul_zero] at this

/-- The hypothesis `v ‖u‖² ≤ uᵀ (c² I) u` holds with `v = c²` (any `ι`). -/
theorem sq_norm_le_smul_one_gram (ι : Type*) [Fintype ι] [DecidableEq ι] (c : ℝ) (u : ι → ℝ) :
    c ^ 2 * ‖u‖ ^ 2 ≤ u ⬝ᵥ (((c • (1 : Matrix ι ι ℝ)) * (c • (1 : Matrix ι ι ℝ))ᵀ) *ᵥ u) := by
  rw [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    Matrix.smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, ← sq]
  exact mul_le_mul_of_nonneg_left (norm_sq_le_sum_mul_self u) (sq_nonneg c)

/-- A one-dimensional instance: `N(0,4)` versus `N(0,1)` on the half-line `{x ≤ 1}`, with
`v = 1`; the right side is `3 · gaussCmpConst (Fin 1)`. -/
example :
    |((stdGaussianPi (Fin 1)).map (((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ ·)).real
        {x | x 0 ≤ 1} -
      ((stdGaussianPi (Fin 1)).map (((1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ ·)).real
        {x | x 0 ≤ 1}| ≤ gaussCmpConst (Fin 1) / 1 * 3 := by
  have h₁ : ∀ u : Fin 1 → ℝ, 1 * ‖u‖ ^ 2 ≤ u ⬝ᵥ
      ((((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
        ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ) *ᵥ u) := fun u ↦ by
    have := sq_norm_le_smul_one_gram (Fin 1) 2 u
    nlinarith [sq_nonneg ‖u‖]
  have h₂ : ∀ u : Fin 1 → ℝ, 1 * ‖u‖ ^ 2 ≤ u ⬝ᵥ
      ((((1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
        ((1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ) *ᵥ u) := fun u ↦ by
    simpa using sq_norm_le_smul_one_gram (Fin 1) 1 u
  have hK : Convex ℝ {x : Fin 1 → ℝ | x 0 ≤ 1} :=
    convex_halfSpace_le (f := fun x : Fin 1 → ℝ ↦ x 0) ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩ 1
  have := abs_real_convex_gaussian_sub_le _ _ one_pos h₁ h₂ hK
  have hE : entryMax (((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *
      ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ -
      ((1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * ((1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ) =
      3 := by
    have h1 : ∀ i j : Fin 1, (1 : Matrix (Fin 1) (Fin 1) ℝ) i j = 1 := fun i j ↦ by
      rw [Subsingleton.elim i j, one_apply_eq]
    haveI : Unique (Fin 1 × Fin 1) :=
      ⟨⟨(0, 0)⟩, fun p ↦ Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
    unfold entryMax
    rw [ciSup_unique]
    norm_num [h1]
  rwa [hE] at this

end StatisticalRL.Probability

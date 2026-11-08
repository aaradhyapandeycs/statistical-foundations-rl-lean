import Formalization.Analysis.TaylorLipschitzHessian
import Formalization.Probability.StdGaussianPi
import Mathlib.Topology.Instances.Matrix

/-!
# Lindeberg replacement for finite discrete laws on `ι → ℝ`

Reusable probability infrastructure (intended integration path
`Formalization/Probability/LindebergFinite.lean`).

Setting: a finite type `X` with weights `p ≥ 0`, `∑ p = 1`, vectors `Y : X → ι → ℝ` and a matrix
`L` such that `Y` (under `p`) and `L Z` (with `Z` standard Gaussian on `ι → ℝ`) have the same first
two moments: `∑ₓ p x Y x i = 0` and `∑ₓ p x Y x i Y x j = (L Lᵀ)ᵢⱼ`. Test functions `f` are `C²`
with `‖Df‖ ≤ L₁` (used only for integrability: it gives linear growth, so no Bochner integral below
is the junk value of a non-integrable function) and `D²f` `L₂`-Lipschitz.

* `abs_sum_sub_integral_le_of_moments` (one-step replacement, any base point `U`):
  `|∑ₓ p x f(U + Y x) − ∫ f(U + L z) dν| ≤ L₂/6 · (∑ₓ p x ‖Y x‖³ + ∫ ‖L z‖³ dν)`.
* `abs_sum_sub_integral_le_of_moments_smul`: the same with scale `b ≥ 0` (factor `b³`).
* `abs_sum_integral_sub_integral_le`: one interpolation step with Gaussian splitting.
* `lindeberg_iid`: for i.i.d. draws `ω : Fin T → X` with weights `∏ₜ p (ω t)`,
  `|E f(T^{-1/2} ∑ₜ Y(ωₜ)) − ∫ f(L z) dν| ≤ L₂/6 · (∑ₓ p x ‖Y x‖³ + ∫ ‖L z‖³ dν) / √T`.

Norms on `ι → ℝ` are Lean's sup norm.
-/

open MeasureTheory ProbabilityTheory Real Matrix
open StatisticalRL.Analysis

namespace StatisticalRL.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Matrix–vector bounds -/

/-- The entrywise `ℓ¹` size `∑ᵢ ∑ₖ |Lᵢₖ|` of a square matrix (bounds its sup-norm operator norm). -/
def matrixAbsSum (L : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ k, |L i k|

omit [DecidableEq ι] in
theorem matrixAbsSum_nonneg (L : Matrix ι ι ℝ) : 0 ≤ matrixAbsSum L :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

omit [DecidableEq ι] in
theorem norm_mulVec_le_matrixAbsSum (L : Matrix ι ι ℝ) (z : ι → ℝ) :
    ‖L *ᵥ z‖ ≤ matrixAbsSum L * ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg (matrixAbsSum_nonneg L) (norm_nonneg z))).2 fun i ↦ ?_
  rw [Real.norm_eq_abs]
  calc |(L *ᵥ z) i| = |∑ k, L i k * z k| := rfl
    _ ≤ ∑ k, |L i k * z k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |L i k| * ‖z‖ := Finset.sum_le_sum fun k _ ↦ by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_apply_le_norm z k) (abs_nonneg _)
    _ = (∑ k, |L i k|) * ‖z‖ := by rw [Finset.sum_mul]
    _ ≤ matrixAbsSum L * ‖z‖ :=
        mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := fun i ↦ ∑ k, |L i k|)
            (fun i _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i))
          (norm_nonneg _)

omit [DecidableEq ι] in
theorem continuous_mulVec (L : Matrix ι ι ℝ) : Continuous fun z : ι → ℝ ↦ L *ᵥ z :=
  Continuous.matrix_mulVec (A := fun _ ↦ L) continuous_const continuous_id

omit [DecidableEq ι] in
theorem mulVec_smul_eq_smul_mulVec (L : Matrix ι ι ℝ) (c : ℝ) (z : ι → ℝ) :
    L *ᵥ (c • z) = (c • L) *ᵥ z := by
  rw [Matrix.mulVec_smul, Matrix.smul_mulVec]

/-! ## Integrability against the standard Gaussian -/

omit [DecidableEq ι] in
theorem integrable_mulVec_apply_stdGaussianPi (L : Matrix ι ι ℝ) (i : ι) :
    Integrable (fun z : ι → ℝ ↦ (L *ᵥ z) i) (stdGaussianPi ι) := by
  simp only [Matrix.mulVec, dotProduct]
  exact integrable_finset_sum _ fun k _ ↦ (integrable_apply_stdGaussianPi k).const_mul _

omit [DecidableEq ι] in
theorem integrable_mulVec_apply_mul_mulVec_apply_stdGaussianPi (L : Matrix ι ι ℝ) (i j : ι) :
    Integrable (fun z : ι → ℝ ↦ (L *ᵥ z) i * (L *ᵥ z) j) (stdGaussianPi ι) := by
  have e : (fun z : ι → ℝ ↦ (L *ᵥ z) i * (L *ᵥ z) j) =
      fun z ↦ ∑ k, ∑ l, L i k * L j l * (z k * z l) := by
    ext z
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    ring
  rw [e]
  exact integrable_finset_sum _ fun k _ ↦ integrable_finset_sum _ fun l _ ↦
    (integrable_apply_mul_apply_stdGaussianPi k l).const_mul _

omit [DecidableEq ι] in
theorem integrable_norm_mulVec_pow_three_stdGaussianPi (L : Matrix ι ι ℝ) :
    Integrable (fun z : ι → ℝ ↦ ‖L *ᵥ z‖ ^ 3) (stdGaussianPi ι) := by
  refine integrable_of_abs_le_one_add_norm_pow_three
    ((continuous_mulVec L).norm.pow 3) (C := matrixAbsSum L ^ 3) fun z ↦ ?_
  have h := norm_mulVec_le_matrixAbsSum L z
  rw [abs_of_nonneg (by positivity)]
  calc ‖L *ᵥ z‖ ^ 3 ≤ (matrixAbsSum L * ‖z‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) h 3
    _ = matrixAbsSum L ^ 3 * ‖z‖ ^ 3 := by ring
    _ ≤ matrixAbsSum L ^ 3 * (1 + ‖z‖ ^ 3) := by
        have := pow_nonneg (matrixAbsSum_nonneg L) 3; nlinarith

omit [DecidableEq ι] in
/-- A function with bounded gradient composed with an affine map of the standard Gaussian is
integrable (linear growth). -/
theorem integrable_comp_add_mulVec_stdGaussianPi {f : (ι → ℝ) → ℝ} (hf : Differentiable ℝ f)
    {L₁ : ℝ} (hL₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ L₁) (U : ι → ℝ) (L : Matrix ι ι ℝ) :
    Integrable (fun z ↦ f (U + L *ᵥ z)) (stdGaussianPi ι) := by
  have hL0 : 0 ≤ L₁ := (norm_nonneg _).trans (hL₁ 0)
  have hM := matrixAbsSum_nonneg L
  refine integrable_of_abs_le_one_add_norm_pow_three
    (hf.continuous.comp (continuous_const.add (continuous_mulVec L)))
    (C := |f 0| + L₁ * ‖U‖ + L₁ * matrixAbsSum L) fun z ↦ ?_
  have h1 := abs_le_of_norm_fderiv_le hf hL₁ (U + L *ᵥ z)
  have h2 : ‖U + L *ᵥ z‖ ≤ ‖U‖ + matrixAbsSum L * ‖z‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl (norm_mulVec_le_matrixAbsSum L z))
  have h3 : ‖z‖ ≤ 1 + ‖z‖ ^ 3 := by
    simpa using pow_le_one_add_pow_three (norm_nonneg z) (k := 1) (by norm_num)
  have hA : L₁ * ‖U + L *ᵥ z‖ ≤ L₁ * (‖U‖ + matrixAbsSum L * ‖z‖) :=
    mul_le_mul_of_nonneg_left h2 hL0
  have hB : (L₁ * matrixAbsSum L) * ‖z‖ ≤ (L₁ * matrixAbsSum L) * (1 + ‖z‖ ^ 3) :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg hL0 hM)
  have hC : 0 ≤ (|f 0| + L₁ * ‖U‖) * ‖z‖ ^ 3 :=
    mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg hL0 (norm_nonneg _))) (by positivity)
  nlinarith

/-! ## One-step replacement -/

variable {X : Type*} [Fintype X]

/-- **One-step Lindeberg replacement.** If `Y` (under the weights `p`) and `L Z` (with `Z` standard
Gaussian) have the same first two moments, then for every base point `U`
`|∑ₓ p x f(U + Y x) − ∫ f(U + L z) dν| ≤ L₂/6 · (∑ₓ p x ‖Y x‖³ + ∫ ‖L z‖³ dν)`. -/
theorem abs_sum_sub_integral_le_of_moments {p : X → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) {Y : X → ι → ℝ} {L : Matrix ι ι ℝ}
    (hY1 : ∀ i, ∑ x, p x * Y x i = 0)
    (hY2 : ∀ i j, ∑ x, p x * (Y x i * Y x j) = (L * L.transpose) i j)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {L₁ : ℝ} (hL₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ L₁) {L₂ : ℝ}
    (hL₂ : ∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ L₂ * ‖x - y‖)
    (U : ι → ℝ) :
    |∑ x, p x * f (U + Y x) - ∫ z, f (U + L *ᵥ z) ∂(stdGaussianPi ι)| ≤
      L₂ / 6 * (∑ x, p x * ‖Y x‖ ^ 3 + ∫ z, ‖L *ᵥ z‖ ^ 3 ∂(stdGaussianPi ι)) := by
  set ν := stdGaussianPi ι
  set D1 := fderiv ℝ f U
  set B := fderiv ℝ (fderiv ℝ f) U
  set e : ι → ι → ℝ := fun i ↦ Pi.single i 1
  set Q : ℝ := ∑ i, ∑ j, (L * L.transpose) i j * B (e i) (e j)
  set P : (ι → ℝ) → ℝ := fun h ↦ f U + D1 h + 1 / 2 * B h h
  set R : (ι → ℝ) → ℝ := fun h ↦ f (U + h) - P h
  have hR : ∀ h, |R h| ≤ L₂ / 6 * ‖h‖ ^ 3 := by
    intro h
    have := abs_taylor_two_le_of_lipschitz_fderiv_fderiv hf hL₂ U h
    calc |R h| = |f (U + h) - f U - D1 h - 1 / 2 * B h h| := by
          congr 1; simp only [R, P]; ring
      _ ≤ _ := this
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  -- coordinate forms
  have hD1 : ∀ h, D1 h = ∑ i, h i * D1 (e i) := fun h ↦ clm_apply_eq_sum D1 h
  have hB : ∀ h, B h h = ∑ i, ∑ j, h i * h j * B (e i) (e j) := fun h ↦
    clm_apply_apply_eq_sum B h h
  -- data side
  have hdata_lin : ∑ x, p x * D1 (Y x) = 0 := by
    calc ∑ x, p x * D1 (Y x) = ∑ x, ∑ i, p x * Y x i * D1 (e i) :=
          Finset.sum_congr rfl fun x _ ↦ by
            rw [hD1, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ = ∑ i, (∑ x, p x * Y x i) * D1 (e i) := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ ↦ by rw [Finset.sum_mul]
      _ = 0 := by simp [hY1]
  have hdata_quad : ∑ x, p x * B (Y x) (Y x) = Q := by
    calc ∑ x, p x * B (Y x) (Y x) = ∑ x, ∑ i, ∑ j, p x * (Y x i * Y x j) * B (e i) (e j) :=
          Finset.sum_congr rfl fun x _ ↦ by
            rw [hB, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ ↦ by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = ∑ i, ∑ j, (∑ x, p x * (Y x i * Y x j)) * B (e i) (e j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ ↦ by rw [Finset.sum_mul]
      _ = Q := by simp only [hY2, Q]
  have hdata : ∑ x, p x * P (Y x) = f U + 1 / 2 * Q := by
    simp only [P, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hp1, hdata_lin]
    have : ∑ x, p x * (1 / 2 * B (Y x) (Y x)) = 1 / 2 * ∑ x, p x * B (Y x) (Y x) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ ↦ by ring
    rw [this, hdata_quad]; ring
  -- Gaussian side
  have hint_i := integrable_mulVec_apply_stdGaussianPi L
  have hint_ij := integrable_mulVec_apply_mul_mulVec_apply_stdGaussianPi L
  have hlin_fun : (fun z : ι → ℝ ↦ D1 (L *ᵥ z)) = fun z ↦ ∑ i, (L *ᵥ z) i * D1 (e i) :=
    funext fun z ↦ hD1 _
  have hquad_fun : (fun z : ι → ℝ ↦ B (L *ᵥ z) (L *ᵥ z)) =
      fun z ↦ ∑ i, ∑ j, (L *ᵥ z) i * (L *ᵥ z) j * B (e i) (e j) :=
    funext fun z ↦ hB _
  have hlin_int : Integrable (fun z : ι → ℝ ↦ D1 (L *ᵥ z)) ν := by
    rw [hlin_fun]; exact integrable_finset_sum _ fun i _ ↦ (hint_i i).mul_const _
  have hquad_int : Integrable (fun z : ι → ℝ ↦ B (L *ᵥ z) (L *ᵥ z)) ν := by
    rw [hquad_fun]
    exact integrable_finset_sum _ fun i _ ↦ integrable_finset_sum _ fun j _ ↦
      (hint_ij i j).mul_const _
  have hgauss_lin : ∫ z, D1 (L *ᵥ z) ∂ν = 0 := by
    rw [hlin_fun, integral_finset_sum _ fun i _ ↦ (hint_i i).mul_const _]
    simp [integral_mul_const, integral_mulVec_apply_stdGaussianPi]
  have hgauss_quad : ∫ z, B (L *ᵥ z) (L *ᵥ z) ∂ν = Q := by
    rw [hquad_fun, integral_finset_sum _ fun i _ ↦ integrable_finset_sum _ fun j _ ↦
      (hint_ij i j).mul_const _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finset_sum _ fun j _ ↦ (hint_ij i j).mul_const _]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_mul_const, integral_mulVec_apply_mul_mulVec_apply_stdGaussianPi]
  have hP_int : Integrable (fun z : ι → ℝ ↦ P (L *ᵥ z)) ν :=
    ((integrable_const _).add hlin_int).add (hquad_int.const_mul _)
  have hgaussP : ∫ z, P (L *ᵥ z) ∂ν = f U + 1 / 2 * Q := by
    have e1 : ∫ z, P (L *ᵥ z) ∂ν = ∫ z, (f U + D1 (L *ᵥ z)) ∂ν +
        ∫ z, 1 / 2 * B (L *ᵥ z) (L *ᵥ z) ∂ν :=
      integral_add ((integrable_const _).add hlin_int) (hquad_int.const_mul _)
    have e2 : ∫ z, (f U + D1 (L *ᵥ z)) ∂ν = ∫ _z, f U ∂ν + ∫ z, D1 (L *ᵥ z) ∂ν :=
      integral_add (integrable_const _) hlin_int
    rw [e1, e2, integral_const, integral_const_mul, hgauss_lin, hgauss_quad]
    simp
  have hf_int : Integrable (fun z ↦ f (U + L *ᵥ z)) ν :=
    integrable_comp_add_mulVec_stdGaussianPi hdiff hL₁ U L
  have hR_int : Integrable (fun z ↦ R (L *ᵥ z)) ν := hf_int.sub hP_int
  have hcube_int := integrable_norm_mulVec_pow_three_stdGaussianPi L
  -- decomposition
  have hsplit_data : ∑ x, p x * f (U + Y x) = f U + 1 / 2 * Q + ∑ x, p x * R (Y x) := by
    rw [← hdata, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by simp only [R]; ring
  have hsplit_gauss : ∫ z, f (U + L *ᵥ z) ∂ν = f U + 1 / 2 * Q + ∫ z, R (L *ᵥ z) ∂ν := by
    rw [← hgaussP, ← integral_add hP_int hR_int]
    exact integral_congr_ae (ae_of_all _ fun z ↦ by simp only [R]; ring)
  have hbd_data : |∑ x, p x * R (Y x)| ≤ L₂ / 6 * ∑ x, p x * ‖Y x‖ ^ 3 := by
    calc |∑ x, p x * R (Y x)| ≤ ∑ x, |p x * R (Y x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, p x * (L₂ / 6 * ‖Y x‖ ^ 3) := Finset.sum_le_sum fun x _ ↦ by
          rw [abs_mul, abs_of_nonneg (hp0 x)]
          exact mul_le_mul_of_nonneg_left (hR _) (hp0 x)
      _ = L₂ / 6 * ∑ x, p x * ‖Y x‖ ^ 3 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ ↦ by ring
  have hbd_gauss : |∫ z, R (L *ᵥ z) ∂ν| ≤ L₂ / 6 * ∫ z, ‖L *ᵥ z‖ ^ 3 ∂ν := by
    rw [← integral_const_mul]
    have := norm_integral_le_of_norm_le (hcube_int.const_mul (L₂ / 6))
      (ae_of_all ν fun z ↦ (by rw [Real.norm_eq_abs]; exact hR _ :
        ‖R (L *ᵥ z)‖ ≤ L₂ / 6 * ‖L *ᵥ z‖ ^ 3))
    simpa [Real.norm_eq_abs] using this
  rw [hsplit_data, hsplit_gauss]
  calc |f U + 1 / 2 * Q + ∑ x, p x * R (Y x) - (f U + 1 / 2 * Q + ∫ z, R (L *ᵥ z) ∂ν)|
      = |∑ x, p x * R (Y x) - ∫ z, R (L *ᵥ z) ∂ν| := by ring_nf
    _ ≤ |∑ x, p x * R (Y x)| + |∫ z, R (L *ᵥ z) ∂ν| := abs_sub _ _
    _ ≤ L₂ / 6 * ∑ x, p x * ‖Y x‖ ^ 3 + L₂ / 6 * ∫ z, ‖L *ᵥ z‖ ^ 3 ∂ν :=
        add_le_add hbd_data hbd_gauss
    _ = _ := by ring

/-- One-step replacement at scale `b ≥ 0`:
`|∑ₓ p x f(U + b Y x) − ∫ f(U + L (b z)) dν| ≤ L₂/6 · b³ · (∑ₓ p x ‖Y x‖³ + ∫ ‖L z‖³ dν)`. -/
theorem abs_sum_sub_integral_le_of_moments_smul {p : X → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) {Y : X → ι → ℝ} {L : Matrix ι ι ℝ}
    (hY1 : ∀ i, ∑ x, p x * Y x i = 0)
    (hY2 : ∀ i j, ∑ x, p x * (Y x i * Y x j) = (L * L.transpose) i j)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {L₁ : ℝ} (hL₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ L₁) {L₂ : ℝ}
    (hL₂ : ∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ L₂ * ‖x - y‖)
    (U : ι → ℝ) {b : ℝ} (hb : 0 ≤ b) :
    |∑ x, p x * f (U + b • Y x) - ∫ z, f (U + L *ᵥ (b • z)) ∂(stdGaussianPi ι)| ≤
      L₂ / 6 * b ^ 3 *
        (∑ x, p x * ‖Y x‖ ^ 3 + ∫ z, ‖L *ᵥ z‖ ^ 3 ∂(stdGaussianPi ι)) := by
  have hY1' : ∀ i, ∑ x, p x * (b • Y x) i = 0 := fun i ↦ by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show ∑ x, p x * (b * Y x i) = b * ∑ x, p x * Y x i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ ↦ by ring, hY1, mul_zero]
  have hY2' : ∀ i j, ∑ x, p x * ((b • Y x) i * (b • Y x) j) =
      ((b • L) * (b • L).transpose) i j := fun i j ↦ by
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_apply]
    rw [← hY2, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  have h := abs_sum_sub_integral_le_of_moments hp0 hp1 hY1' hY2' hf hL₁ hL₂ U
  simp_rw [mulVec_smul_eq_smul_mulVec]
  have e1 : ∑ x, p x * ‖b • Y x‖ ^ 3 = b ^ 3 * ∑ x, p x * ‖Y x‖ ^ 3 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by rw [norm_smul, Real.norm_of_nonneg hb]; ring
  have e2 : ∫ z, ‖(b • L) *ᵥ z‖ ^ 3 ∂(stdGaussianPi ι) =
      b ^ 3 * ∫ z, ‖L *ᵥ z‖ ^ 3 ∂(stdGaussianPi ι) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun z ↦ by
      simp only [Matrix.smul_mulVec, norm_smul, Real.norm_of_nonneg hb]; ring)
  rw [e1, e2] at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-! ## One interpolation step -/

/-- **One Lindeberg interpolation step.** For `a` real and `b ≥ 0`, replacing the Gaussian
`L(√(a²+b²) Z)` by `L(a Z) + b Y` costs at most `L₂/6 · b³ · (∑ₓ p x ‖Y x‖³ + ∫ ‖L z‖³ dν)`. -/
theorem abs_sum_integral_sub_integral_le {p : X → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) {Y : X → ι → ℝ} {L : Matrix ι ι ℝ}
    (hY1 : ∀ i, ∑ x, p x * Y x i = 0)
    (hY2 : ∀ i j, ∑ x, p x * (Y x i * Y x j) = (L * L.transpose) i j)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {L₁ : ℝ} (hL₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ L₁) {L₂ : ℝ}
    (hL₂ : ∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ L₂ * ‖x - y‖)
    (S : ι → ℝ) (a : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    |∑ x, p x * ∫ z, f (S + b • Y x + L *ᵥ (a • z)) ∂(stdGaussianPi ι) -
        ∫ z, f (S + L *ᵥ (√(a ^ 2 + b ^ 2) • z)) ∂(stdGaussianPi ι)| ≤
      L₂ / 6 * b ^ 3 *
        (∑ x, p x * ‖Y x‖ ^ 3 + ∫ z, ‖L *ᵥ z‖ ^ 3 ∂(stdGaussianPi ι)) := by
  set ν := stdGaussianPi ι
  set M := ∑ x, p x * ‖Y x‖ ^ 3 + ∫ z, ‖L *ᵥ z‖ ^ 3 ∂ν
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hint : ∀ (U : ι → ℝ) (c : ℝ), Integrable (fun z ↦ f (U + L *ᵥ (c • z))) ν := by
    intro U c
    simp_rw [mulVec_smul_eq_smul_mulVec]
    exact integrable_comp_add_mulVec_stdGaussianPi hdiff hL₁ U _
  -- Gaussian splitting
  set F : (ι → ℝ) → ℝ := fun w ↦ f (S + L *ᵥ w)
  have hFm : Measurable F :=
    (hdiff.continuous.comp (continuous_const.add (continuous_mulVec L))).measurable
  obtain ⟨hprod_int, hprod_eq⟩ := integral_stdGaussianPi_prod_add a b hFm (hint S _)
  have hG_int : Integrable (fun z ↦ ∫ z', F (a • z + b • z') ∂ν) ν :=
    hprod_int.integral_prod_left
  have hgauss : ∫ z, f (S + L *ᵥ (√(a ^ 2 + b ^ 2) • z)) ∂ν =
      ∫ z, ∫ z', F (a • z + b • z') ∂ν ∂ν := by
    rw [← integral_prod _ hprod_int]
    exact hprod_eq.symm
  -- data side as one integral
  have hAx : ∀ x, Integrable (fun z ↦ f (S + L *ᵥ (a • z) + b • Y x)) ν := by
    intro x
    refine (hint (S + b • Y x) a).congr (ae_of_all _ fun z ↦ ?_)
    simp only; rw [add_right_comm]
  have hdata : ∑ x, p x * ∫ z, f (S + b • Y x + L *ᵥ (a • z)) ∂ν =
      ∫ z, ∑ x, p x * f (S + L *ᵥ (a • z) + b • Y x) ∂ν := by
    rw [integral_finset_sum _ fun x _ ↦ (hAx x).const_mul _]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun z ↦ by simp only; rw [add_right_comm])
  have hA_int : Integrable (fun z ↦ ∑ x, p x * f (S + L *ᵥ (a • z) + b • Y x)) ν := by
    exact integrable_finset_sum _ fun x _ ↦ (hAx x).const_mul _
  rw [hdata, hgauss, ← integral_sub hA_int hG_int]
  have hpt : ∀ z, ‖∑ x, p x * f (S + L *ᵥ (a • z) + b • Y x) -
      ∫ z', F (a • z + b • z') ∂ν‖ ≤ L₂ / 6 * b ^ 3 * M := by
    intro z
    have h := abs_sum_sub_integral_le_of_moments_smul hp0 hp1 hY1 hY2 hf hL₁ hL₂
      (S + L *ᵥ (a • z)) hb
    have e : ∫ z', F (a • z + b • z') ∂ν = ∫ z', f (S + L *ᵥ (a • z) + L *ᵥ (b • z')) ∂ν :=
      integral_congr_ae (ae_of_all _ fun z' ↦ by simp only [F, Matrix.mulVec_add, add_assoc])
    rw [Real.norm_eq_abs, e]
    exact h
  have := norm_integral_le_of_norm_le_const (μ := ν) (ae_of_all _ hpt)
  simpa [Real.norm_eq_abs] using this

/-! ## The i.i.d. Lindeberg theorem -/

omit [DecidableEq ι] in
private theorem sum_fin_succ_snoc' {n : ℕ} {β : Type*} [AddCommMonoid β]
    (F : (Fin (n + 1) → X) → β) :
    ∑ ω, F ω = ∑ ω : Fin n → X, ∑ x : X, F (Fin.snoc ω x) := by
  rw [← (Fin.snocEquiv fun _ ↦ X).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

omit [DecidableEq ι] in
theorem sum_prod_weights {p : X → ℝ} (hp1 : ∑ x, p x = 1) (n : ℕ) :
    ∑ ω : Fin n → X, ∏ t, p (ω t) = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin n ↦ (Finset.univ : Finset X)) (fun _ x ↦ p x)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  simp [hp1]

/-- **Lindeberg's theorem for i.i.d. finite discrete summands on `ι → ℝ`.** If `Y` (under `p`)
and `L Z` (`Z` standard Gaussian) have the same first two moments, then for every `T ≥ 1` and every
`C²` test function with `‖Df‖ ≤ L₁` and `L₂`-Lipschitz `D²f`,
`|E f(T^{-1/2} ∑ₜ Y(ωₜ)) − ∫ f(L z) dν| ≤ L₂/6 · (∑ₓ p x ‖Y x‖³ + ∫ ‖L z‖³ dν) / √T`,
where `ω : Fin T → X` has i.i.d. coordinates with law `p`. -/
theorem lindeberg_iid {p : X → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) {Y : X → ι → ℝ} {L : Matrix ι ι ℝ}
    (hY1 : ∀ i, ∑ x, p x * Y x i = 0)
    (hY2 : ∀ i j, ∑ x, p x * (Y x i * Y x j) = (L * L.transpose) i j)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {L₁ : ℝ} (hL₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ L₁) {L₂ : ℝ}
    (hL₂ : ∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ L₂ * ‖x - y‖)
    {T : ℕ} (hT : 0 < T) :
    |∑ ω : Fin T → X, (∏ t, p (ω t)) * f ((√T)⁻¹ • ∑ t, Y (ω t)) -
        ∫ z, f (L *ᵥ z) ∂(stdGaussianPi ι)| ≤
      L₂ / 6 * (∑ x, p x * ‖Y x‖ ^ 3 + ∫ z, ‖L *ᵥ z‖ ^ 3 ∂(stdGaussianPi ι)) / √T := by
  set ν := stdGaussianPi ι
  set M := ∑ x, p x * ‖Y x‖ ^ 3 + ∫ z, ‖L *ᵥ z‖ ^ 3 ∂ν
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hsT : 0 < √(T : ℝ) := Real.sqrt_pos.2 hT0
  set s : ℝ := (√(T : ℝ))⁻¹
  have hs0 : 0 ≤ s := inv_nonneg.2 hsT.le
  set c : ℕ → ℝ := fun k ↦ √(((T : ℝ) - k) / T)
  set H : ℕ → ℝ := fun k ↦ ∑ ω : Fin k → X, (∏ t, p (ω t)) *
    ∫ z, f (s • ∑ t, Y (ω t) + L *ᵥ (c k • z)) ∂ν
  set b := L₂ / 6 * s ^ 3 * M
  have hstep : ∀ k, k < T → |H (k + 1) - H k| ≤ b := by
    intro k hk
    have hc : c k = √(c (k + 1) ^ 2 + s ^ 2) := by
      simp only [c, s]
      rw [Real.sq_sqrt (div_nonneg (by
          have : ((k + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast hk
          linarith) hT0.le), inv_pow, Real.sq_sqrt hT0.le]
      congr 1
      push_cast
      field_simp
      ring
    have hsplit : H (k + 1) = ∑ ω : Fin k → X, (∏ t, p (ω t)) *
        ∑ x, p x * ∫ z, f (s • ∑ t, Y (ω t) + s • Y x + L *ᵥ (c (k + 1) • z)) ∂ν := by
      simp only [H]
      rw [sum_fin_succ_snoc']
      refine Finset.sum_congr rfl fun ω _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, smul_add]
      ring
    have hdiff : H (k + 1) - H k = ∑ ω : Fin k → X, (∏ t, p (ω t)) *
        (∑ x, p x * ∫ z, f (s • ∑ t, Y (ω t) + s • Y x + L *ᵥ (c (k + 1) • z)) ∂ν -
          ∫ z, f (s • ∑ t, Y (ω t) + L *ᵥ (√(c (k + 1) ^ 2 + s ^ 2) • z)) ∂ν) := by
      rw [hsplit, ← hc]
      simp only [H, mul_sub, Finset.sum_sub_distrib]
    rw [hdiff]
    calc |∑ ω : Fin k → X, (∏ t, p (ω t)) * _| ≤ ∑ ω : Fin k → X, |(∏ t, p (ω t)) * _| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω : Fin k → X, (∏ t, p (ω t)) * b := Finset.sum_le_sum fun ω _ ↦ by
          have hw : 0 ≤ ∏ t, p (ω t) := Finset.prod_nonneg fun t _ ↦ hp0 _
          rw [abs_mul, abs_of_nonneg hw]
          exact mul_le_mul_of_nonneg_left
            (abs_sum_integral_sub_integral_le hp0 hp1 hY1 hY2 hf hL₁ hL₂ _ _ hs0) hw
      _ = b := by rw [← Finset.sum_mul, sum_prod_weights hp1, one_mul]
  have htel : ∀ k, k ≤ T → |H k - H 0| ≤ k * b := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (Nat.le_of_succ_le hk)
      have h2 := hstep k hk
      calc |H (k + 1) - H 0| = |(H (k + 1) - H k) + (H k - H 0)| := by ring_nf
        _ ≤ |H (k + 1) - H k| + |H k - H 0| := abs_add_le _ _
        _ ≤ b + k * b := add_le_add h2 h1
        _ = ((k + 1 : ℕ) : ℝ) * b := by push_cast; ring
  have hHT : H T = ∑ ω : Fin T → X, (∏ t, p (ω t)) * f (s • ∑ t, Y (ω t)) := by
    simp only [H, c, sub_self, zero_div, Real.sqrt_zero, zero_smul, Matrix.mulVec_zero,
      add_zero, integral_const, probReal_univ, one_smul]
  have hH0 : H 0 = ∫ z, f (L *ᵥ z) ∂ν := by
    simp only [H, c, Nat.cast_zero, sub_zero, div_self hT0.ne', Real.sqrt_one, one_smul,
      Finset.univ_eq_empty, Finset.sum_empty, smul_zero, zero_add, Finset.prod_empty, one_mul]
    simp
  have hfin := htel T le_rfl
  rw [hHT, hH0] at hfin
  calc _ ≤ (T : ℝ) * b := hfin
    _ = L₂ / 6 * M / √T := by
        simp only [b, s]
        have hTs : √(T : ℝ) * √T = T := Real.mul_self_sqrt hT0.le
        nth_rewrite 1 [← hTs]
        field_simp

end StatisticalRL.Probability

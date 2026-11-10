import Formalization.Probability.ConvexLindebergReservoirBase
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Mixed third derivatives of Gaussian smoothings and a localized Lindeberg swap

Infrastructure toward the all-convex-sets route to Theorem 7.11 (`thm:Berry-Esseen-linear`); it
proves no statement of the book and has no statement-index entry. The constructions here (a
three-fold split of a Gaussian smoothing, integration by parts in two of the three Gaussian
factors, and a segment-local Taylor bound) are standard Lindeberg/Bentkus-type smoothing tools,
written out from first principles; they are not taken from a cited paper.

Contents:
* `abs_taylor_two_le_of_hasDerivAt`: a one-dimensional second-order Taylor bound with the third
  derivative controlled only on `[0, 1]`;
* `dirDeriv h G = fun y ↦ DG(y) h`, the class `SmoothBdd` (`C^∞` with every derivative bounded) and
  its closure under directional derivatives and Gaussian smoothing;
* `dirDeriv_gaussSmooth`, `dirDeriv_gaussSmooth_eq_integral` (Gaussian integration by parts in a
  direction `h = S₀ v`);
* `dirDeriv_three_eq`: the third directional derivative of a three-fold Gaussian smoothing, with
  one derivative on the test function and one Gaussian weight `⟨v, w⟩` on each of two of the
  three Gaussian factors;
* `taylorRem`, `sum_sub_integral_eq_taylorRem` (exact moment cancellation in a Lindeberg swap)
  and `abs_taylorRem_le_of_dirDeriv` (local Taylor remainder bound);
* support of the derivatives of the convex sandwich functions in the convex shell, and the
  smoothing inequality for tests with that support property;
* the fourth Gaussian moment constant `gaussFourthMoment`.
-/

open MeasureTheory ProbabilityTheory Real Matrix Metric Filter Topology
open StatisticalRL.Analysis

namespace StatisticalRL.Probability.ReservoirSharp

open StatisticalRL.Probability

/-! ## A local second-order Taylor bound on `[0, 1]` -/

/-- **Second-order Taylor bound on `[0,1]` with a local third derivative.**
If `g' = g₁`, `g₁' = g₂`, `g₂' = g₃` and `|g₃| ≤ M` on `[0, 1]`, then
`|g 1 − g 0 − g₁ 0 − g₂ 0 / 2| ≤ M / 6`. -/
theorem abs_taylor_two_le_of_hasDerivAt {g g₁ g₂ g₃ : ℝ → ℝ}
    (h₀ : ∀ t, HasDerivAt g (g₁ t) t) (h₁ : ∀ t, HasDerivAt g₁ (g₂ t) t)
    (h₂ : ∀ t, HasDerivAt g₂ (g₃ t) t) {M : ℝ}
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g₃ t| ≤ M) :
    |g 1 - g 0 - g₁ 0 - g₂ 0 / 2| ≤ M / 6 := by
  have d2 : ∀ t, HasDerivAt (fun s ↦ g₂ s - g₂ 0) (g₃ t) t := fun t ↦ (h₂ t).sub_const _
  have f2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖g₂ t - g₂ 0‖ ≤ M * t := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun s ↦ g₂ s - g₂ 0)
      (f' := g₃) (fun t _ ↦ (d2 t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (d2 t).hasDerivWithinAt) (B' := fun _ ↦ M) ?_ ?_ ?_
    · simp
    · intro t; simpa using (hasDerivAt_id t).const_mul M
    · intro t ht; rw [Real.norm_eq_abs]; exact hM t (Set.Ico_subset_Icc_self ht)
  have d1 : ∀ t, HasDerivAt (fun s ↦ g₁ s - g₁ 0 - s * g₂ 0) (g₂ t - g₂ 0) t := by
    intro t
    have := ((h₁ t).sub_const (g₁ 0)).sub ((hasDerivAt_id t).mul_const (g₂ 0))
    simpa using this
  have f1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖g₁ t - g₁ 0 - t * g₂ 0‖ ≤ M * t ^ 2 / 2 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s ↦ g₁ s - g₁ 0 - s * g₂ 0) (f' := fun s ↦ g₂ s - g₂ 0)
      (fun t _ ↦ (d1 t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (d1 t).hasDerivWithinAt) (B' := fun t ↦ M * t) ?_ ?_ ?_
    · simp
    · intro t
      have := ((hasDerivAt_pow 2 t).const_mul M).div_const 2
      convert this using 1; push_cast; ring
    · intro t ht; exact f2 t (Set.Ico_subset_Icc_self ht)
  have d0 : ∀ t, HasDerivAt (fun s ↦ g s - g 0 - s * g₁ 0 - s ^ 2 / 2 * g₂ 0)
      (g₁ t - g₁ 0 - t * g₂ 0) t := by
    intro t
    have := (((h₀ t).sub_const (g 0)).sub ((hasDerivAt_id t).mul_const (g₁ 0))).sub
      (((hasDerivAt_pow 2 t).div_const 2).mul_const (g₂ 0))
    convert this using 1; push_cast; ring
  have f0 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖g t - g 0 - t * g₁ 0 - t ^ 2 / 2 * g₂ 0‖ ≤ M * t ^ 3 / 6 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s ↦ g s - g 0 - s * g₁ 0 - s ^ 2 / 2 * g₂ 0)
      (f' := fun s ↦ g₁ s - g₁ 0 - s * g₂ 0)
      (fun t _ ↦ (d0 t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (d0 t).hasDerivWithinAt) (B' := fun t ↦ M * t ^ 2 / 2) ?_ ?_ ?_
    · simp
    · intro t
      have := ((hasDerivAt_pow 3 t).const_mul M).div_const 6
      convert this using 1; push_cast; ring
    · intro t ht; exact f1 t (Set.Ico_subset_Icc_self ht)
  have key := f0 1 ⟨zero_le_one, le_rfl⟩
  rw [Real.norm_eq_abs] at key
  calc |g 1 - g 0 - g₁ 0 - g₂ 0 / 2| = |g 1 - g 0 - 1 * g₁ 0 - 1 ^ 2 / 2 * g₂ 0| := by
        ring_nf
    _ ≤ M * 1 ^ 3 / 6 := key
    _ = M / 6 := by ring

/-! ## Directional derivatives and the class `SmoothBdd` -/

section Directional

variable {ι : Type*} [Fintype ι]

/-- Directional derivative `y ↦ DG(y) h`. -/
noncomputable def dirDeriv (h : ι → ℝ) (G : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  fun y ↦ fderiv ℝ G y h

/-- `C^∞` with every iterated derivative bounded. -/
def SmoothBdd (G : (ι → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧ ∀ k : ℕ, ∃ C, ∀ y, ‖iteratedFDeriv ℝ k G y‖ ≤ C

namespace SmoothBdd

variable {G : (ι → ℝ) → ℝ}

theorem contDiff_nat (hG : SmoothBdd G) (n : ℕ) : ContDiff ℝ n G := contDiff_infty.1 hG.1 n

theorem differentiable (hG : SmoothBdd G) : Differentiable ℝ G :=
  (hG.contDiff_nat 1).differentiable le_rfl

theorem continuous (hG : SmoothBdd G) : Continuous G := hG.1.continuous

theorem continuous_fderiv (hG : SmoothBdd G) : Continuous (fderiv ℝ G) :=
  (hG.contDiff_nat 1).continuous_fderiv le_rfl

theorem bound0 (hG : SmoothBdd G) : ∃ C, ∀ y, ‖G y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hG.2 0
  exact ⟨C, fun y ↦ by rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]; exact hC y⟩

theorem bound1 (hG : SmoothBdd G) : ∃ C, ∀ y, ‖fderiv ℝ G y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hG.2 1
  exact ⟨C, fun y ↦ by rw [norm_fderiv_eq_norm_iteratedFDeriv_one]; exact hC y⟩

theorem bound2 (hG : SmoothBdd G) : ∃ C, ∀ y, ‖fderiv ℝ (fderiv ℝ G) y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hG.2 2
  refine ⟨C, fun y ↦ ?_⟩
  rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fderiv ℝ (fderiv ℝ G)),
    norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
  exact hC y

/-- Directional derivatives stay in the class. -/
theorem dirDeriv (hG : SmoothBdd G) (h : ι → ℝ) : SmoothBdd (dirDeriv h G) := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ G) :=
    hG.1.fderiv_right (by simp)
  refine ⟨hf.clm_apply contDiff_const, fun k ↦ ?_⟩
  obtain ⟨C, hC⟩ := hG.2 (k + 1)
  refine ⟨‖h‖ * C, fun y ↦ ?_⟩
  have := norm_iteratedFDeriv_clm_apply_const (c := h) (n := k) (N := k) (x := y)
    ((contDiff_infty.1 hf k).contDiffAt) le_rfl
  refine this.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [norm_iteratedFDeriv_fderiv]
  exact hC y

/-- Gaussian smoothing stays in the class. -/
theorem gaussSmooth (hG : SmoothBdd G) {ι' : Type*} [Fintype ι'] (R : Matrix ι ι' ℝ) :
    SmoothBdd (StatisticalRL.Probability.gaussSmooth G R) := by
  refine ⟨contDiff_infty.2 fun n ↦ contDiff_gaussSmooth (hG.contDiff_nat n)
    (fun j _ ↦ hG.2 j) R, fun k ↦ ?_⟩
  exact bdd_iteratedFDeriv_gaussSmooth (n := k) (hG.contDiff_nat k) (fun j _ ↦ hG.2 j) R k le_rfl

end SmoothBdd

theorem hasDerivAt_dirDeriv_line {G : (ι → ℝ) → ℝ} (hG : Differentiable ℝ G)
    (x h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ G (x + s • h)) (dirDeriv h G (x + t • h)) t :=
  (hG (x + t • h)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_add_smul x h t)

/-- The second directional derivative is the Hessian on `(h, h)`. -/
theorem dirDeriv_dirDeriv_eq {G : (ι → ℝ) → ℝ} (hG : SmoothBdd G) (h x : ι → ℝ) :
    dirDeriv h (dirDeriv h G) x = fderiv ℝ (fderiv ℝ G) x h h := by
  have hd : DifferentiableAt ℝ (fderiv ℝ G) x :=
    ((hG.contDiff_nat 2).fderiv_right (m := 1) (by norm_num)).differentiable le_rfl x
  show fderiv ℝ (fun y ↦ fderiv ℝ G y h) x h = _
  rw [fderiv_clm_apply hd (differentiableAt_const h)]
  simp

variable {ι' : Type*} [Fintype ι']

/-- `D_h` commutes with Gaussian smoothing. -/
theorem dirDeriv_gaussSmooth {G : (ι → ℝ) → ℝ} (hG : SmoothBdd G) (R : Matrix ι ι' ℝ)
    (h : ι → ℝ) : dirDeriv h (gaussSmooth G R) = gaussSmooth (dirDeriv h G) R := by
  funext x
  obtain ⟨C₀, hC₀⟩ := hG.bound0
  obtain ⟨C₁, hC₁⟩ := hG.bound1
  have hd := hasFDerivAt_gaussSmooth hG.differentiable hG.continuous_fderiv hC₀ hC₁ R x
  simp only [dirDeriv]
  rw [hd.fderiv]
  unfold StatisticalRL.Probability.gaussSmooth
  refine ContinuousLinearMap.integral_apply ?_ h
  exact Integrable.of_bound
    (hG.continuous_fderiv.comp (continuous_const.add (continuous_mulVec_const R))).aestronglyMeasurable
    C₁ (ae_of_all _ fun z ↦ hC₁ _)

/-- **Gaussian integration by parts in a direction.** If `R v = h`, then
`D_h (gaussSmooth G R) x = E[⟨v, Z⟩ G(x + R Z)]`. -/
theorem dirDeriv_gaussSmooth_eq_integral {G : (ι → ℝ) → ℝ} (hG : SmoothBdd G)
    (R : Matrix ι ι' ℝ) {h : ι → ℝ} {v : ι' → ℝ} (hv : R *ᵥ v = h) (x : ι → ℝ) :
    dirDeriv h (gaussSmooth G R) x =
      ∫ z, (∑ j, v j * z j) * G (x + R *ᵥ z) ∂stdGaussianPi ι' := by
  classical
  obtain ⟨C₀, hC₀⟩ := hG.bound0
  obtain ⟨C₁, hC₁⟩ := hG.bound1
  have hRc := continuous_mulVec_const R
  set Lc : (ι' → ℝ) →L[ℝ] (ι → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin R)
  set g : (ι' → ℝ) → ℝ := fun z ↦ G (x + R *ᵥ z) with hg_def
  set g' : (ι' → ℝ) → (ι' → ℝ) →L[ℝ] ℝ := fun z ↦ (fderiv ℝ G (x + R *ᵥ z)).comp Lc
    with hg'_def
  have hg : ∀ z, HasFDerivAt g (g' z) z := fun z ↦
    (hG.differentiable (x + R *ᵥ z)).hasFDerivAt.comp z (Lc.hasFDerivAt.const_add x)
  have hg'c : Continuous g' :=
    (hG.continuous_fderiv.comp (continuous_const.add hRc)).clm_comp continuous_const
  have hIBP := integral_sum_mul_smul_eq_integral_hasFDerivAt hg hg'c (C₀ := C₀)
    (C₁ := C₁ * ‖Lc‖) (fun z ↦ hC₀ _)
    (fun z ↦ (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hC₁ _) (norm_nonneg _))) v
  simp only [smul_eq_mul] at hIBP
  rw [hIBP, dirDeriv_gaussSmooth hG R h]
  unfold StatisticalRL.Probability.gaussSmooth
  simp only [dirDeriv]
  congr 1
  funext z
  rw [← hv]
  rfl

/-- **Third directional derivative of a three-fold Gaussian smoothing.** With `S₀ v = h`,
`D_h³ (gaussSmooth (gaussSmooth (gaussSmooth φ S₀) S₀) S₀) y =
E_w E_{w'}[⟨v,w⟩ ⟨v,w'⟩ (gaussSmooth (D_h φ) S₀)(y + S₀ w + S₀ w')]`. -/
theorem dirDeriv_three_eq {φ : (ι → ℝ) → ℝ} (hφ : SmoothBdd φ) (S₀ : Matrix ι ι' ℝ)
    {h : ι → ℝ} {v : ι' → ℝ} (hv : S₀ *ᵥ v = h) (y : ι → ℝ) :
    dirDeriv h (dirDeriv h (dirDeriv h
        (gaussSmooth (gaussSmooth (gaussSmooth φ S₀) S₀) S₀))) y =
      ∫ w, (∑ j, v j * w j) * ∫ w', (∑ j, v j * w' j) *
        gaussSmooth (dirDeriv h φ) S₀ (y + S₀ *ᵥ w + S₀ *ᵥ w')
          ∂stdGaussianPi ι' ∂stdGaussianPi ι' := by
  have h1 : SmoothBdd (gaussSmooth φ S₀) := hφ.gaussSmooth S₀
  have h2 : SmoothBdd (gaussSmooth (gaussSmooth φ S₀) S₀) := h1.gaussSmooth S₀
  rw [dirDeriv_gaussSmooth h2, dirDeriv_gaussSmooth (h2.dirDeriv h),
    dirDeriv_gaussSmooth_eq_integral ((h2.dirDeriv h).dirDeriv h) S₀ hv]
  congr 1
  funext w
  congr 1
  rw [dirDeriv_gaussSmooth h1, dirDeriv_gaussSmooth_eq_integral (h1.dirDeriv h) S₀ hv,
    dirDeriv_gaussSmooth hφ]

end Directional

/-! ## Exact moment cancellation in a Lindeberg swap -/

section Swap

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [Fintype X]

/-- Second-order Taylor remainder of `F` at `U` in the direction `h`. -/
noncomputable def taylorRem (F : (ι → ℝ) → ℝ) (U h : ι → ℝ) : ℝ :=
  F (U + h) - F U - fderiv ℝ F U h - 1 / 2 * fderiv ℝ (fderiv ℝ F) U h h

/-- **Exact moment cancellation.** If `Y` (under `p`) and `L Z` have the same first two moments and
`F` is bounded and continuous, the swap difference equals the difference of the Taylor
remainders. -/
theorem sum_sub_integral_eq_taylorRem {p : X → ℝ} (hp1 : ∑ x, p x = 1) {Y : X → ι → ℝ}
    {L : Matrix ι ι ℝ} (hY1 : ∀ i, ∑ x, p x * Y x i = 0)
    (hY2 : ∀ i j, ∑ x, p x * (Y x i * Y x j) = (L * L.transpose) i j)
    {F : (ι → ℝ) → ℝ} (hFc : Continuous F) {C₀ : ℝ} (hF0 : ∀ x, |F x| ≤ C₀) (U : ι → ℝ) :
    (∑ x, p x * F (U + Y x) - ∫ z, F (U + L *ᵥ z) ∂(stdGaussianPi ι) =
      ∑ x, p x * taylorRem F U (Y x) - ∫ z, taylorRem F U (L *ᵥ z) ∂(stdGaussianPi ι)) ∧
    Integrable (fun z ↦ taylorRem F U (L *ᵥ z)) (stdGaussianPi ι) := by
  set ν := stdGaussianPi ι
  set D1 := fderiv ℝ F U
  set B := fderiv ℝ (fderiv ℝ F) U
  set e : ι → ι → ℝ := fun i ↦ Pi.single i 1
  set Q : ℝ := ∑ i, ∑ j, (L * L.transpose) i j * B (e i) (e j)
  set P : (ι → ℝ) → ℝ := fun h ↦ F U + D1 h + 1 / 2 * B h h
  have hR : ∀ h, taylorRem F U h = F (U + h) - P h := fun h ↦ by
    simp only [taylorRem, P, D1, B]; ring
  have hD1 : ∀ h, D1 h = ∑ i, h i * D1 (e i) := fun h ↦ clm_apply_eq_sum D1 h
  have hB : ∀ h, B h h = ∑ i, ∑ j, h i * h j * B (e i) (e j) := fun h ↦
    clm_apply_apply_eq_sum B h h
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
  have hdata : ∑ x, p x * P (Y x) = F U + 1 / 2 * Q := by
    simp only [P, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hp1, hdata_lin]
    have : ∑ x, p x * (1 / 2 * B (Y x) (Y x)) = 1 / 2 * ∑ x, p x * B (Y x) (Y x) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ ↦ by ring
    rw [this, hdata_quad]; ring
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
  have hgaussP : ∫ z, P (L *ᵥ z) ∂ν = F U + 1 / 2 * Q := by
    have e1 : ∫ z, P (L *ᵥ z) ∂ν = ∫ z, (F U + D1 (L *ᵥ z)) ∂ν +
        ∫ z, 1 / 2 * B (L *ᵥ z) (L *ᵥ z) ∂ν :=
      integral_add ((integrable_const _).add hlin_int) (hquad_int.const_mul _)
    have e2 : ∫ z, (F U + D1 (L *ᵥ z)) ∂ν = ∫ _z, F U ∂ν + ∫ z, D1 (L *ᵥ z) ∂ν :=
      integral_add (integrable_const _) hlin_int
    rw [e1, e2, integral_const, integral_const_mul, hgauss_lin, hgauss_quad]
    simp
  have hf_int : Integrable (fun z ↦ F (U + L *ᵥ z)) ν :=
    Integrable.of_bound (hFc.comp (continuous_const.add (continuous_mulVec L))).aestronglyMeasurable
      C₀ (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hF0 _)
  have hR_int : Integrable (fun z ↦ taylorRem F U (L *ᵥ z)) ν := by
    simp_rw [hR]; exact hf_int.sub hP_int
  refine ⟨?_, hR_int⟩
  have hsplit_data : ∑ x, p x * F (U + Y x) =
      F U + 1 / 2 * Q + ∑ x, p x * taylorRem F U (Y x) := by
    rw [← hdata, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by rw [hR]; ring
  have hsplit_gauss : ∫ z, F (U + L *ᵥ z) ∂ν =
      F U + 1 / 2 * Q + ∫ z, taylorRem F U (L *ᵥ z) ∂ν := by
    rw [← hgaussP, ← integral_add hP_int hR_int]
    exact integral_congr_ae (ae_of_all _ fun z ↦ by simp only [hR]; ring)
  rw [hsplit_data, hsplit_gauss]
  ring

omit [DecidableEq ι] in
/-- **Local Taylor remainder bound.** If the third directional derivative of `F` in the direction
`h` is bounded by `M` on the segment `[U, U + h]`, then `|taylorRem F U h| ≤ M / 6`. -/
theorem abs_taylorRem_le_of_dirDeriv {F : (ι → ℝ) → ℝ} (hF : SmoothBdd F) (U h : ι → ℝ)
    {M : ℝ} (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |dirDeriv h (dirDeriv h (dirDeriv h F)) (U + t • h)| ≤ M) :
    |taylorRem F U h| ≤ M / 6 := by
  have h1 := hF.dirDeriv h
  have h2 := h1.dirDeriv h
  have key := abs_taylor_two_le_of_hasDerivAt
    (g := fun t ↦ F (U + t • h)) (g₁ := fun t ↦ dirDeriv h F (U + t • h))
    (g₂ := fun t ↦ dirDeriv h (dirDeriv h F) (U + t • h))
    (g₃ := fun t ↦ dirDeriv h (dirDeriv h (dirDeriv h F)) (U + t • h))
    (hasDerivAt_dirDeriv_line hF.differentiable U h) (hasDerivAt_dirDeriv_line h1.differentiable U h)
    (hasDerivAt_dirDeriv_line h2.differentiable U h) hM
  simp only [zero_smul, add_zero, one_smul] at key
  rw [dirDeriv_dirDeriv_eq hF h U] at key
  simp only [taylorRem]
  convert key using 2
  simp only [dirDeriv]
  ring

end Swap

/-! ## Support of the sandwich derivatives in the convex shell -/

section Support

variable {ι : Type*} [Fintype ι]

/-- The closed convex shell `cthickening δ K ∩ cthickening δ (interior K)ᶜ`. -/
def shellSet (δ : ℝ) (K : Set (ι → ℝ)) : Set (ι → ℝ) :=
  cthickening δ K ∩ cthickening δ (interior K)ᶜ

theorem isClosed_shellSet (δ : ℝ) (K : Set (ι → ℝ)) : IsClosed (shellSet δ K) :=
  isClosed_cthickening.inter isClosed_cthickening

theorem measurableSet_shellSet (δ : ℝ) (K : Set (ι → ℝ)) : MeasurableSet (shellSet δ K) :=
  (isClosed_shellSet δ K).measurableSet

/-- A function that is locally constant at `x` has zero derivative there. -/
theorem fderiv_eq_zero_of_eventually_eq {φ : (ι → ℝ) → ℝ} {x : ι → ℝ} {c : ℝ}
    (h : ∀ᶠ y in 𝓝 x, φ y = c) : fderiv ℝ φ x = 0 := by
  rw [Filter.EventuallyEq.fderiv_eq (f := fun _ ↦ c) h]
  exact fderiv_const_apply c

/-- Upper sandwich: the derivative vanishes off the shell. -/
theorem fderiv_eq_zero_of_upper {φ : (ι → ℝ) → ℝ} {K : Set (ι → ℝ)} {ε : ℝ}
    (h1 : ∀ x ∈ K, φ x = 1) (h0 : ∀ x ∉ thickening ε K, φ x = 0) {x : ι → ℝ}
    (hx : x ∉ shellSet ε K) : fderiv ℝ φ x = 0 := by
  simp only [shellSet, Set.mem_inter_iff, not_and_or] at hx
  rcases hx with hx | hx
  · have hx' : x ∈ (closure (thickening ε K))ᶜ := fun hc ↦
      hx (closure_thickening_subset_cthickening ε K hc)
    refine fderiv_eq_zero_of_eventually_eq (c := 0) ?_
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx'] with y hy
    exact h0 y fun hy' ↦ hy (subset_closure hy')
  · have hx' : x ∈ interior K := by
      by_contra hc
      exact hx (self_subset_cthickening _ hc)
    refine fderiv_eq_zero_of_eventually_eq (c := 1) ?_
    filter_upwards [isOpen_interior.mem_nhds hx'] with y hy
    exact h1 y (interior_subset hy)

/-- Lower sandwich: the derivative vanishes off the shell. -/
theorem fderiv_eq_zero_of_lower {φ : (ι → ℝ) → ℝ} {K : Set (ι → ℝ)} {ε : ℝ}
    (h1 : ∀ x, closedBall x ε ⊆ K → φ x = 1) (h0 : ∀ x ∉ K, φ x = 0) {x : ι → ℝ}
    (hx : x ∉ shellSet ε K) : fderiv ℝ φ x = 0 := by
  simp only [shellSet, Set.mem_inter_iff, not_and_or] at hx
  rcases hx with hx | hx
  · have hx' : x ∈ (closure K)ᶜ := fun hc ↦ hx (closure_subset_cthickening ε K hc)
    refine fderiv_eq_zero_of_eventually_eq (c := 0) ?_
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx'] with y hy
    exact h0 y fun hy' ↦ hy (subset_closure hy')
  · refine fderiv_eq_zero_of_eventually_eq (c := 1) ?_
    filter_upwards [isClosed_cthickening.isOpen_compl.mem_nhds hx] with y hy
    exact h1 y (closedBall_subset_of_mem_inner hy)

/-- **Smoothing inequality for tests supported in the shell** (any set `K`). As
`abs_pexp_indicator_sub_le_of_smooth`, but the smooth comparison `hsm` is only required for tests
whose first derivative vanishes off the `ε`-shell of `K`. -/
theorem abs_pexp_indicator_sub_le_of_smooth_supp {κ : Type*} [Fintype κ] [DecidableEq κ]
    {X : κ → Type*} [∀ i, Fintype (X i)] {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (Z : (∀ i, X i) → ι → ℝ) (ν' : Measure (ι → ℝ)) [IsProbabilityMeasure ν'] {ε σ Δ : ℝ}
    (hε : 0 < ε) (K : Set (ι → ℝ))
    (hsh : ν'.real (shellSet ε K) ≤ σ)
    (hsm : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      (∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) →
      (∀ (k : ℕ) (x : ι → ℝ),
        ‖iteratedFDeriv ℝ k φ x‖ ≤ ConvexSmoothIndicator.sandwichConst ι k / ε ^ k) →
      (∀ x ∉ shellSet ε K, fderiv ℝ φ x = 0) →
      |Stein.pexp p (fun ω ↦ φ (Z ω)) - ∫ y, φ y ∂ν'| ≤ Δ) :
    |Stein.pexp p (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (Z ω)) - ν'.real K| ≤ Δ + σ := by
  obtain ⟨φu, hu_s, hu01, hu1, hu0, hud⟩ :=
    ConvexSmoothIndicator.exists_smooth_sandwich_upper K hε
  have hup1 : Stein.pexp p (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (Z ω)) ≤
      Stein.pexp p (fun ω ↦ φu (Z ω)) :=
    Stein.pexp_mono hp0 fun ω ↦ by
      by_cases h : Z ω ∈ K
      · rw [Set.indicator_of_mem h, hu1 _ h]
      · rw [Set.indicator_of_notMem h]; exact (hu01 _).1
  have hup2 := (abs_le.1 (hsm φu hu_s hu01 hud fun x hx ↦ fderiv_eq_zero_of_upper hu1 hu0 hx)).2
  have hthick : IsOpen (thickening ε K) := isOpen_thickening
  have hup3 : ∫ y, φu y ∂ν' ≤ ν'.real (thickening ε K) := by
    rw [← integral_indicator_one hthick.measurableSet]
    refine integral_mono (integrable_of_continuous_mem_Icc hu_s.continuous hu01)
      ((integrable_const (1 : ℝ)).indicator hthick.measurableSet) fun x ↦ ?_
    by_cases h : x ∈ thickening ε K
    · rw [Set.indicator_of_mem h]; exact (hu01 x).2
    · rw [Set.indicator_of_notMem h, hu0 x h]
  have hup4 : ν'.real (thickening ε K) ≤ ν'.real K + ν'.real (shellSet ε K) :=
    (measureReal_mono (thickening_subset_union_shell K hε.le)).trans (measureReal_union_le _ _)
  obtain ⟨φl, hl_s, hl01, hl1, hl0, hld⟩ :=
    ConvexSmoothIndicator.exists_smooth_sandwich_lower K hε
  have hMo : IsOpen (cthickening ε (interior K)ᶜ)ᶜ := isClosed_cthickening.isOpen_compl
  have hlo1 : Stein.pexp p (fun ω ↦ φl (Z ω)) ≤
      Stein.pexp p (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (Z ω)) :=
    Stein.pexp_mono hp0 fun ω ↦ by
      by_cases h : Z ω ∈ K
      · rw [Set.indicator_of_mem h]; exact (hl01 _).2
      · rw [Set.indicator_of_notMem h, hl0 _ h]
  have hlo2 := (abs_le.1 (hsm φl hl_s hl01 hld fun x hx ↦ fderiv_eq_zero_of_lower hl1 hl0 hx)).1
  have hlo3 : ν'.real (cthickening ε (interior K)ᶜ)ᶜ ≤ ∫ y, φl y ∂ν' := by
    rw [← integral_indicator_one hMo.measurableSet]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hMo.measurableSet)
      (integrable_of_continuous_mem_Icc hl_s.continuous hl01) fun x ↦ ?_
    by_cases h : x ∈ (cthickening ε (interior K)ᶜ)ᶜ
    · rw [Set.indicator_of_mem h, hl1 x (closedBall_subset_of_mem_inner h)]; rfl
    · rw [Set.indicator_of_notMem h]; exact (hl01 x).1
  have hlo4 : ν'.real K ≤ ν'.real (cthickening ε (interior K)ᶜ)ᶜ + ν'.real (shellSet ε K) :=
    (measureReal_mono (subset_inner_union_shell K ε)).trans (measureReal_union_le _ _)
  rw [abs_le]; constructor <;> linarith

/-- If `y + t h` lies in the `ε`-shell for some `t ∈ [0,1]`, then `y` lies in the
`(‖h‖ + ε)`-shell. -/
theorem mem_shellSet_of_add_smul {K : Set (ι → ℝ)} {ε : ℝ} (hε : 0 ≤ ε) {y h : ι → ℝ} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hy : y + t • h ∈ shellSet ε K) :
    y ∈ shellSet (‖h‖ + ε) K := by
  have hd : dist y (y + t • h) ≤ ‖h‖ := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  exact ⟨cthickening_cthickening_subset (norm_nonneg h) hε _
      (mem_cthickening_of_dist_le _ _ _ _ hy.1 hd),
    cthickening_cthickening_subset (norm_nonneg h) hε _
      (mem_cthickening_of_dist_le _ _ _ _ hy.2 hd)⟩

/-- The open `ε`-thickening of the `δ`-shell lies in the `(ε + δ)`-shell. -/
theorem thickening_shellSet_subset {K : Set (ι → ℝ)} (ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    thickening ε (shellSet δ K) ⊆ shellSet (ε + δ) K := by
  intro x hx
  exact ⟨thickening_subset_cthickening _ _
      (thickening_cthickening_subset ε hδ _
        (thickening_subset_of_subset ε (Set.inter_subset_left : shellSet δ K ⊆ cthickening δ K) hx)),
    thickening_subset_cthickening _ _
      (thickening_cthickening_subset ε hδ _
        (thickening_subset_of_subset ε
          (Set.inter_subset_right : shellSet δ K ⊆ cthickening δ (interior K)ᶜ) hx))⟩

end Support

/-! ## The fourth Gaussian moment -/

section Fourth

variable {ι : Type*} [Fintype ι]

/-- `E‖Z‖⁴` for a standard Gaussian `Z` on `ι → ℝ` (sup norm). -/
noncomputable def gaussFourthMoment (ι : Type*) [Fintype ι] : ℝ :=
  ∫ z, ‖z‖ ^ 4 ∂stdGaussianPi ι

theorem norm_pow_four_le_sum (z : ι → ℝ) : ‖z‖ ^ 4 ≤ ∑ i, |z i| ^ 4 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim z 0]
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i ↦ |z i|) Finset.univ_nonempty
  have hz : ‖z‖ = |z i| := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j ↦ ?_)
      (abs_apply_le_norm z i)
    rw [Real.norm_eq_abs]; exact hi j (Finset.mem_univ j)
  rw [hz]
  exact Finset.single_le_sum (f := fun j ↦ |z j| ^ 4) (fun j _ ↦ by positivity) (Finset.mem_univ i)

theorem integrable_norm_pow_four_stdGaussianPi :
    Integrable (fun z : ι → ℝ ↦ ‖z‖ ^ 4) (stdGaussianPi ι) := by
  refine (integrable_finset_sum Finset.univ fun i _ ↦
    integrable_abs_apply_pow_stdGaussianPi (ι := ι) i 4).mono'
    (continuous_norm.pow 4).aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_pow_four_le_sum z

theorem gaussFourthMoment_nonneg : 0 ≤ gaussFourthMoment ι :=
  integral_nonneg fun _ ↦ by positivity

/-- `E‖L Z‖⁴ ≤ matrixAbsSum L ⁴ · E‖Z‖⁴`, and `‖L Z‖⁴` is integrable. -/
theorem integral_norm_mulVec_pow_four_le [DecidableEq ι] (L : Matrix ι ι ℝ) :
    Integrable (fun z ↦ ‖L *ᵥ z‖ ^ 4) (stdGaussianPi ι) ∧
    ∫ z, ‖L *ᵥ z‖ ^ 4 ∂stdGaussianPi ι ≤ matrixAbsSum L ^ 4 * gaussFourthMoment ι := by
  have hb : ∀ z : ι → ℝ, ‖L *ᵥ z‖ ^ 4 ≤ matrixAbsSum L ^ 4 * ‖z‖ ^ 4 := fun z ↦ by
    calc ‖L *ᵥ z‖ ^ 4 ≤ (matrixAbsSum L * ‖z‖) ^ 4 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_mulVec_le_matrixAbsSum L z) 4
      _ = _ := by ring
  have hI : Integrable (fun z ↦ ‖L *ᵥ z‖ ^ 4) (stdGaussianPi ι) :=
    (integrable_norm_pow_four_stdGaussianPi.const_mul (matrixAbsSum L ^ 4)).mono'
      ((continuous_norm.comp (continuous_mulVec L)).pow 4).aestronglyMeasurable
      (ae_of_all _ fun z ↦ by rw [Real.norm_of_nonneg (by positivity)]; exact hb z)
  refine ⟨hI, ?_⟩
  rw [gaussFourthMoment, ← integral_const_mul]
  exact integral_mono hI (integrable_norm_pow_four_stdGaussianPi.const_mul _) hb

end Fourth

end StatisticalRL.Probability.ReservoirSharp

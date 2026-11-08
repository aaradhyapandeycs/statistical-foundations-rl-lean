import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Second-order Taylor bound with a Lipschitz Hessian

Reusable analysis infrastructure (intended integration path
`Formalization/Analysis/TaylorLipschitzHessian.lean`).

* `abs_taylor_two_le_of_lipschitz_fderiv_fderiv`: for `f : E → ℝ` that is `C²` with
  `‖D²f x − D²f y‖ ≤ L₂‖x − y‖`,
  `|f (u + h) − f u − Df u h − ½ D²f u h h| ≤ L₂/6 · ‖h‖³`.
* `abs_sub_le_of_norm_fderiv_le`, `abs_le_of_norm_fderiv_le`: a gradient bound `‖Df‖ ≤ L₁` gives
  the Lipschitz bound and linear growth `|f x| ≤ |f 0| + L₁‖x‖`.
* `clm_apply_eq_sum`, `clm_apply_apply_eq_sum`: coordinate expansion of a linear and a bilinear
  form on `ι → ℝ`.
-/

open Set

namespace StatisticalRL.Analysis

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of `t ↦ u + t • h`. -/
theorem hasDerivAt_add_smul (u h : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ u + s • h) h t := by
  simpa using ((hasDerivAt_id t).smul_const h).const_add u

/-- **Second-order Taylor bound with a Lipschitz Hessian.** If `f : E → ℝ` is `C²` and its
second derivative is `L₂`-Lipschitz, then
`|f (u + h) − f u − Df(u) h − ½ D²f(u) h h| ≤ L₂/6 · ‖h‖³`. -/
theorem abs_taylor_two_le_of_lipschitz_fderiv_fderiv {f : E → ℝ} (hf : ContDiff ℝ 2 f) {L₂ : ℝ}
    (hL : ∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ L₂ * ‖x - y‖)
    (u h : E) :
    |f (u + h) - f u - fderiv ℝ f u h - (1 / 2) * fderiv ℝ (fderiv ℝ f) u h h| ≤
      L₂ / 6 * ‖h‖ ^ 3 := by
  set D1 := fderiv ℝ f
  set D2 := fderiv ℝ D1
  have hd0 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd1 : Differentiable ℝ D1 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  -- derivative of `t ↦ D1 (u + t h) h`
  have hφ1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ D1 (u + s • h) h) (D2 (u + t • h) h h) t := by
    intro t
    have hc : HasDerivAt (fun s : ℝ ↦ D1 (u + s • h)) (D2 (u + t • h) h) t :=
      (hd1 (u + t • h)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_add_smul u h t)
    simpa using hc.clm_apply (hasDerivAt_const t h)
  have hφ0 : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ f (u + s • h)) (D1 (u + t • h) h) t := fun t ↦
    (hd0 (u + t • h)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_add_smul u h t)
  set c := L₂ * ‖h‖ ^ 3
  -- first fence: `ψ₁ t = D1(u+th)h − D1 u h − t D2 u h h`, `|ψ₁ t| ≤ c t²/2`
  set ψ1 : ℝ → ℝ := fun t ↦ D1 (u + t • h) h - D1 u h - t * D2 u h h
  have hψ1 : ∀ t : ℝ, HasDerivAt ψ1 (D2 (u + t • h) h h - D2 u h h) t := by
    intro t
    have := ((hφ1 t).sub_const (D1 u h)).sub ((hasDerivAt_id t).mul_const (D2 u h h))
    simpa [ψ1] using this
  have hbound1 : ∀ t ∈ Ico (0 : ℝ) 1, ‖D2 (u + t • h) h h - D2 u h h‖ ≤ c * t := by
    intro t ht
    have h1 : ‖D2 (u + t • h) - D2 u‖ ≤ L₂ * (t * ‖h‖) := by
      have := hL (u + t • h) u
      rwa [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1] at this
    have h2 : ‖(D2 (u + t • h) - D2 u) h h‖ ≤ ‖D2 (u + t • h) - D2 u‖ * ‖h‖ * ‖h‖ :=
      ((D2 (u + t • h) - D2 u) h).le_opNorm h |>.trans
        (mul_le_mul_of_nonneg_right (((D2 (u + t • h) - D2 u)).le_opNorm h) (norm_nonneg h))
    have h3 : ‖D2 (u + t • h) - D2 u‖ * ‖h‖ * ‖h‖ ≤ L₂ * (t * ‖h‖) * ‖h‖ * ‖h‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (norm_nonneg h)) (norm_nonneg h)
    calc ‖D2 (u + t • h) h h - D2 u h h‖ = ‖(D2 (u + t • h) - D2 u) h h‖ := by simp
      _ ≤ L₂ * (t * ‖h‖) * ‖h‖ * ‖h‖ := h2.trans h3
      _ = c * t := by simp only [c]; ring
  have hfence1 : ∀ t ∈ Icc (0 : ℝ) 1, ‖ψ1 t‖ ≤ c * t ^ 2 / 2 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun t _ ↦ (hψ1 t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hψ1 t).hasDerivWithinAt) (B' := fun t ↦ c * t) ?_ ?_ hbound1
    · simp [ψ1]
    · intro t
      have := ((hasDerivAt_pow 2 t).const_mul c).div_const 2
      convert this using 1; ring
  -- second fence: `ψ₀ t = f(u+th) − f u − t D1 u h − t²/2 D2 u h h`, `|ψ₀ t| ≤ c t³/6`
  set ψ0 : ℝ → ℝ := fun t ↦ f (u + t • h) - f u - t * D1 u h - t ^ 2 / 2 * D2 u h h
  have hψ0 : ∀ t : ℝ, HasDerivAt ψ0 (ψ1 t) t := by
    intro t
    have := (((hφ0 t).sub_const (f u)).sub ((hasDerivAt_id t).mul_const (D1 u h))).sub
      (((hasDerivAt_pow 2 t).div_const 2).mul_const (D2 u h h))
    convert this using 1
    simp only [ψ1]; push_cast; ring
  have hfence0 : ∀ t ∈ Icc (0 : ℝ) 1, ‖ψ0 t‖ ≤ c * t ^ 3 / 6 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun t _ ↦ (hψ0 t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hψ0 t).hasDerivWithinAt) (B' := fun t ↦ c * t ^ 2 / 2) ?_ ?_
      (fun t ht ↦ hfence1 t (Ico_subset_Icc_self ht))
    · simp [ψ0]
    · intro t
      have := ((hasDerivAt_pow 3 t).const_mul c).div_const 6
      convert this using 1; push_cast; ring
  have key := hfence0 1 ⟨zero_le_one, le_rfl⟩
  simp only [ψ0, one_smul, one_mul, one_pow, Real.norm_eq_abs] at key
  calc |f (u + h) - f u - D1 u h - 1 / 2 * D2 u h h|
      = |f (u + h) - f u - D1 u h - D2 u h h / 2| := by ring_nf
    _ ≤ c / 6 := by
        rw [show D2 u h h / 2 = 2⁻¹ * D2 u h h by ring]; simpa [one_div] using key
    _ = L₂ / 6 * ‖h‖ ^ 3 := by simp only [c]; ring

/-- A gradient bound gives the Lipschitz bound `|f y − f x| ≤ L₁ ‖y − x‖`. -/
theorem abs_sub_le_of_norm_fderiv_le {f : E → ℝ} (hf : Differentiable ℝ f) {L₁ : ℝ}
    (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L₁) (x y : E) : |f y - f x| ≤ L₁ * ‖y - x‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (fun z _ ↦ hf z) (fun z _ ↦ hL z)
    convex_univ (mem_univ x) (mem_univ y)
  simpa [Real.norm_eq_abs] using this

/-- A gradient bound gives linear growth `|f x| ≤ |f 0| + L₁ ‖x‖`. -/
theorem abs_le_of_norm_fderiv_le {f : E → ℝ} (hf : Differentiable ℝ f) {L₁ : ℝ}
    (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L₁) (x : E) : |f x| ≤ |f 0| + L₁ * ‖x‖ := by
  have h := abs_sub_le_of_norm_fderiv_le hf hL 0 x
  rw [sub_zero] at h
  have := abs_sub_abs_le_abs_sub (f x) (f 0)
  linarith

end Taylor

section Coordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate expansion of a continuous linear map on `ι → ℝ`. -/
theorem clm_apply_eq_sum_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : (ι → ℝ) →L[ℝ] F) (v : ι → ℝ) : D v = ∑ i, v i • D (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have e : (Pi.single i (v i) : ι → ℝ) = v i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
    ext j; by_cases h : j = i <;> simp [Pi.single_apply, h]
  rw [e, map_smul]

/-- Coordinate expansion of a linear form on `ι → ℝ`. -/
theorem clm_apply_eq_sum (D : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    D v = ∑ i, v i * D (Pi.single i 1) := by
  simpa only [smul_eq_mul] using clm_apply_eq_sum_smul D v

/-- Coordinate expansion of a bilinear form on `ι → ℝ`. -/
theorem clm_apply_apply_eq_sum (B : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) (v w : ι → ℝ) :
    B v w = ∑ i, ∑ j, v i * w j * B (Pi.single i 1) (Pi.single j 1) := by
  rw [clm_apply_eq_sum_smul B v, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ContinuousLinearMap.smul_apply, clm_apply_eq_sum _ w, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end Coordinates

end StatisticalRL.Analysis

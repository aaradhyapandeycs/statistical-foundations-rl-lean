import Formalization.Probability.ConvexLindebergReservoir
import Formalization.Probability.GaussianMixedThird
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Reservoir Lindeberg swap, pass 2: multivariate convex Berry–Esseen at `n^{-1/3}`

Infrastructure toward the all-convex-sets route to Theorem 7.11 (`thm:Berry-Esseen-linear`); it
is not Theorem 7.11, proves no statement of the book and has no statement-index entry. The
argument (a Lindeberg replacement with a Gaussian reservoir, a localized third-order swap bound and
a bootstrap that uses the pass-1 bound `n^{-1/4}` as an anti-concentration input) is a construction
in the Bentkus/Lindeberg tradition written out from first principles, not taken from a cited paper.

Setting as in `ConvexLindebergReservoir.lean`: independent centred summands `Y i (ω i)` with finite
laws `p i`, covariances `L i (L i)ᵀ`, sup norms `≤ B / √n`, and Gaussian twins satisfying
`ReservoirCond e L c r₀`. Main export (`abs_pexp_convex_sub_twinLaw_le_third`): for every convex
`K` (measurable or not) and every `n ≥ 1`,

  `|P(∑ᵢ Yᵢ ∈ K) − N(0, ∑ᵢ Lᵢ Lᵢᵀ)(K)| ≤ reservoirThirdConst ι c r₀ B · n^{-1/3}`,

with a constant depending only on `|ι|`, `c`, `r₀` and `B`.

Proof outline. Smoothing at scale `ε = n^{-1/3}` with the convex sandwich functions, whose first
derivatives live in the `ε`-shell of `K`. The hybrid step at reservoir size `j = n − 1 − k` is
bounded in three ways:
* `j ≥ max (max r₀ 1) ⌈n^{2/3}⌉`: smoothing by the whole reservoir (pass-1 bound `j^{-3/2}`);
* `max r₀ 1 ≤ j < ⌈n^{2/3}⌉`: the **mixed bound**. The reservoir smoothing is split into three
  independent thirds; two Gaussian derivatives fall on two thirds (integration by parts), one
  derivative falls on the test function and is supported in the shell, and the third third is kept
  for anti-concentration. The resulting shell probabilities of the hybrid prefix plus a Gaussian are
  bounded by the pass-1 telescoping applied to a **modified family** (index `e k` removed, the
  future twins scaled by `3^{-1/2}`), giving `O(n^{-1/4})`. The step costs `O(n^{-5/12} / j)`,
  which sums to `O(n^{-5/12} log n) = O(n^{-1/3})`;
* `j < max r₀ 1`: the unsmoothed third-derivative bound.
-/

open MeasureTheory ProbabilityTheory Real Matrix Metric Filter
open StatisticalRL.Analysis

namespace StatisticalRL.Probability.ReservoirSharp

open StatisticalRL.Probability

/-! ## Product expectations and integrals -/

section Pexp

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*} [∀ i, Fintype (X i)]

/-- `pexp` (a finite weighted sum) commutes with a Bochner integral. -/
theorem pexp_integral (p : ∀ i, X i → ℝ) {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : (∀ i, X i) → α → ℝ) (hf : ∀ ω, Integrable (f ω) μ) :
    Stein.pexp p (fun ω ↦ ∫ a, f ω a ∂μ) = ∫ a, Stein.pexp p (fun ω ↦ f ω a) ∂μ := by
  unfold Stein.pexp
  rw [integral_finset_sum _ fun ω _ ↦ (hf ω).const_mul _]
  exact Finset.sum_congr rfl fun ω _ ↦ (integral_const_mul _ _).symm

end Pexp

/-! ## Integrability helpers -/

section Integrability

variable {ι' : Type*} [Fintype ι']

theorem integrable_abs_sum_mul (v : ι' → ℝ) :
    Integrable (fun w : ι' → ℝ ↦ |∑ j, v j * w j|) (stdGaussianPi ι') :=
  (integrable_finset_sum _ fun j _ ↦ (integrable_apply_stdGaussianPi j).const_mul (v j)).abs

theorem continuous_abs_sum_mul (v : ι' → ℝ) : Continuous fun w : ι' → ℝ ↦ |∑ j, v j * w j| :=
  (continuous_finset_sum _ fun j _ ↦ continuous_const.mul (continuous_apply j)).abs

/-- `|⟨v, w⟩| · g w` is integrable for `g` continuous with `|g| ≤ C`. -/
theorem integrable_abs_sum_mul_mul {v : ι' → ℝ} {g : (ι' → ℝ) → ℝ} (hg : Continuous g) {C : ℝ}
    (hgC : ∀ w, |g w| ≤ C) :
    Integrable (fun w ↦ |∑ j, v j * w j| * g w) (stdGaussianPi ι') := by
  refine ((integrable_abs_sum_mul v).mul_const C).mono'
    ((continuous_abs_sum_mul v).mul hg).aestronglyMeasurable (ae_of_all _ fun w ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_abs]
  exact mul_le_mul_of_nonneg_left (hgC w) (abs_nonneg _)

/-- `E|⟨v, Z⟩|² ≤ ∑ vⱼ²`. -/
theorem integral_abs_sum_mul_sq_le (v : ι' → ℝ) :
    (∫ w, |∑ j, v j * w j| ∂stdGaussianPi ι') ^ 2 ≤ ∑ j, v j ^ 2 := by
  have h0 : 0 ≤ ∫ w, |∑ j, v j * w j| ∂stdGaussianPi ι' := integral_nonneg fun _ ↦ abs_nonneg _
  calc (∫ w, |∑ j, v j * w j| ∂stdGaussianPi ι') ^ 2 ≤ (√(∑ j, v j ^ 2)) ^ 2 :=
        pow_le_pow_left₀ h0 (integral_abs_sum_mul_le v) 2
    _ = ∑ j, v j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)

variable {ι : Type*} [Fintype ι]

/-- The indicator of a measurable set along an affine Gaussian map is integrable. -/
theorem integrable_indicator_affine {A : Set (ι → ℝ)} (hA : MeasurableSet A) (S₀ : Matrix ι ι' ℝ)
    (c : ι → ℝ) :
    Integrable (fun w ↦ A.indicator (fun _ ↦ (1 : ℝ)) (c + S₀ *ᵥ w)) (stdGaussianPi ι') := by
  refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun w ↦ ?_)
  · exact ((measurable_const.indicator hA).comp
      (continuous_const.add (continuous_mulVec_const S₀)).measurable).aestronglyMeasurable
  · by_cases h : c + S₀ *ᵥ w ∈ A <;> simp [h]

end Integrability

/-! ## The averaged mixed third-order bound for one direction -/

section Mixed

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*} [∀ i, Fintype (X i)]
  {ι : Type*} [Fintype ι] {ι' : Type*} [Fintype ι']

/-- **Averaged mixed bound.** Let `F = gaussSmooth (gaussSmooth (gaussSmooth φ S₀) S₀) S₀` with
`S₀ v = h`, let `Dφ` be bounded by `D` and vanish off the `ε`-shell of `K`, and let the prefix
`P` plus the Gaussian `S₀ Z` have shell probabilities `≤ σ₀ + Csh δ`. Then the averaged Taylor
remainder satisfies `E|taylorRem F P h| ≤ D ‖h‖ (∑ vⱼ²) (σ₀ + Csh (ε + (‖h‖ + ε))) / 6`. -/
theorem pexp_abs_taylorRem_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (P : (∀ i, X i) → ι → ℝ) (S₀ : Matrix ι ι' ℝ) {φ : (ι → ℝ) → ℝ} (hφ : SmoothBdd φ)
    {K : Set (ι → ℝ)} {ε D : ℝ} (hε : 0 < ε) (hD : ∀ y, ‖fderiv ℝ φ y‖ ≤ D)
    (hsupp : ∀ y ∉ shellSet ε K, fderiv ℝ φ y = 0) {σ₀ Csh : ℝ}
    (hσ : ∀ δ, 0 ≤ δ → ∀ u : ι → ℝ, Stein.pexp p (fun ω ↦ ∫ w,
      (shellSet δ K).indicator (fun _ ↦ (1 : ℝ)) (P ω + S₀ *ᵥ w + u) ∂stdGaussianPi ι') ≤
        σ₀ + Csh * δ)
    {h : ι → ℝ} {v : ι' → ℝ} (hv : S₀ *ᵥ v = h) :
    Stein.pexp p (fun ω ↦
        |taylorRem (gaussSmooth (gaussSmooth (gaussSmooth φ S₀) S₀) S₀) (P ω) h|) ≤
      D * ‖h‖ * (∑ j, v j ^ 2) * (σ₀ + Csh * (ε + (‖h‖ + ε))) / 6 := by
  set γ := stdGaussianPi ι'
  set F := gaussSmooth (gaussSmooth (gaussSmooth φ S₀) S₀) S₀ with hF_def
  have hF : SmoothBdd F := ((hφ.gaussSmooth S₀).gaussSmooth S₀).gaussSmooth S₀
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  set δ₁ := ε + (‖h‖ + ε) with hδ₁
  have hδ₁0 : 0 ≤ δ₁ := by positivity
  set σ₁ := σ₀ + Csh * δ₁ with hσ₁
  have hS₀c := continuous_mulVec_const S₀
  -- the continuous majorant `χ` of the fattened shell
  obtain ⟨χ, hχs, hχ01, hχ1, hχ0, -⟩ :=
    ConvexSmoothIndicator.exists_smooth_sandwich_upper (shellSet (‖h‖ + ε) K) hε
  have hχc : Continuous χ := hχs.continuous
  have hχle : ∀ y, χ y ≤ (shellSet δ₁ K).indicator (fun _ ↦ (1 : ℝ)) y := by
    intro y
    by_cases hy : y ∈ thickening ε (shellSet (‖h‖ + ε) K)
    · rw [Set.indicator_of_mem (thickening_shellSet_subset ε (by positivity) hy)]
      exact (hχ01 y).2
    · rw [hχ0 y hy]
      exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hχb : ∀ y, |χ y| ≤ 1 := fun y ↦ by
    rw [abs_of_nonneg (hχ01 y).1]; exact (hχ01 y).2
  -- the derivative of `φ` along the segment
  have hdir : ∀ y, ∀ t ∈ Set.Icc (0 : ℝ) 1, |dirDeriv h φ (y + t • h)| ≤ D * ‖h‖ * χ y := by
    intro y t ht
    by_cases hm : y + t • h ∈ shellSet ε K
    · rw [hχ1 y (mem_shellSet_of_add_smul hε.le ht hm), mul_one]
      calc |dirDeriv h φ (y + t • h)| = ‖fderiv ℝ φ (y + t • h) h‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ φ (y + t • h)‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ D * ‖h‖ := mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)
    · simp only [dirDeriv, hsupp _ hm, ContinuousLinearMap.zero_apply, abs_zero]
      exact mul_nonneg (mul_nonneg hD0 (norm_nonneg _)) (hχ01 y).1
  -- `Θ = gaussSmooth χ S₀`
  set Θ := gaussSmooth χ S₀ with hΘ_def
  have hΘc : Continuous Θ := continuous_gaussSmooth hχc (fun y ↦ by
    rw [Real.norm_eq_abs]; exact hχb y) S₀
  have hΘ01 : ∀ y, 0 ≤ Θ y ∧ Θ y ≤ 1 := fun y ↦ by
    refine ⟨integral_nonneg fun w ↦ (hχ01 _).1, ?_⟩
    have := norm_gaussSmooth_le (φ := χ) (fun y ↦ by rw [Real.norm_eq_abs]; exact hχb y) S₀ y
    exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at this)
  have hΘb : ∀ y, |Θ y| ≤ 1 := fun y ↦ by rw [abs_of_nonneg (hΘ01 y).1]; exact (hΘ01 y).2
  -- `Ψ = gaussSmooth (D_h φ) S₀`
  have hφ1 := hφ.dirDeriv h
  obtain ⟨Cψ, hCψ⟩ := hφ1.bound0
  have hψc : Continuous (dirDeriv h φ) := hφ1.continuous
  have hΨ : ∀ y, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |gaussSmooth (dirDeriv h φ) S₀ (y + t • h)| ≤ D * ‖h‖ * Θ y := by
    intro y t ht
    unfold StatisticalRL.Probability.gaussSmooth
    rw [hΘ_def]
    unfold StatisticalRL.Probability.gaussSmooth
    rw [← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (ae_of_all _ fun w ↦ abs_nonneg _) ?_ (ae_of_all _ fun w ↦ ?_))
    · exact (integrable_of_continuous_mem_Icc (hχc.comp (continuous_const.add hS₀c))
        (fun w ↦ hχ01 _)).const_mul _
    · show |dirDeriv h φ (y + t • h + S₀ *ᵥ w)| ≤ D * ‖h‖ * χ (y + S₀ *ᵥ w)
      rw [show y + t • h + S₀ *ᵥ w = (y + S₀ *ᵥ w) + t • h by abel]
      exact hdir _ t ht
  -- the majorant of the third directional derivative
  have hDh : 0 ≤ D * ‖h‖ := mul_nonneg hD0 (norm_nonneg _)
  have hgb : ∀ x w w', |D * ‖h‖ * Θ (x + S₀ *ᵥ w + S₀ *ᵥ w')| ≤ D * ‖h‖ := fun x w w' ↦ by
    rw [abs_mul, abs_of_nonneg hDh]
    exact mul_le_of_le_one_right hDh (hΘb _)
  have hinner_int : ∀ x w, Integrable
      (fun w' ↦ |∑ j, v j * w' j| * (D * ‖h‖ * Θ (x + S₀ *ᵥ w + S₀ *ᵥ w'))) γ := fun x w ↦
    integrable_abs_sum_mul_mul (continuous_const.mul (hΘc.comp
      ((continuous_const.add continuous_const).add hS₀c))) (hgb x w)
  set E₁ := ∫ w', |∑ j, v j * w' j| ∂γ with hE₁
  have hE₁0 : 0 ≤ E₁ := integral_nonneg fun _ ↦ abs_nonneg _
  have hIc : ∀ x, Continuous (fun w ↦
      ∫ w', |∑ j, v j * w' j| * (D * ‖h‖ * Θ (x + S₀ *ᵥ w + S₀ *ᵥ w')) ∂γ) := by
    intro x
    refine continuous_of_dominated (bound := fun w' ↦ |∑ j, v j * w' j| * (D * ‖h‖))
      (fun w ↦ (hinner_int x w).aestronglyMeasurable) (fun w ↦ ae_of_all _ fun w' ↦ ?_)
      ((integrable_abs_sum_mul v).mul_const _) (ae_of_all _ fun w' ↦ ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_abs]
      exact mul_le_mul_of_nonneg_left (hgb x w w') (abs_nonneg _)
    · exact continuous_const.mul (continuous_const.mul (hΘc.comp
        ((continuous_const.add hS₀c).add continuous_const)))
  have hIb : ∀ x w, |∫ w', |∑ j, v j * w' j| * (D * ‖h‖ * Θ (x + S₀ *ᵥ w + S₀ *ᵥ w')) ∂γ| ≤
      E₁ * (D * ‖h‖) := by
    intro x w
    have := norm_integral_le_of_norm_le ((integrable_abs_sum_mul v).mul_const (D * ‖h‖))
      (ae_of_all γ fun w' ↦ (by
        rw [Real.norm_eq_abs, abs_mul, abs_abs]
        exact mul_le_mul_of_nonneg_left (hgb x w w') (abs_nonneg _) :
        ‖|∑ j, v j * w' j| * (D * ‖h‖ * Θ (x + S₀ *ᵥ w + S₀ *ᵥ w'))‖ ≤
          |∑ j, v j * w' j| * (D * ‖h‖)))
    rw [Real.norm_eq_abs, integral_mul_const] at this
    exact this
  have houter_int : ∀ x, Integrable (fun w ↦ |∑ j, v j * w j| *
      ∫ w', |∑ j, v j * w' j| * (D * ‖h‖ * Θ (x + S₀ *ᵥ w + S₀ *ᵥ w')) ∂γ) γ := fun x ↦
    integrable_abs_sum_mul_mul (hIc x) (hIb x)
  set Mx : (ι → ℝ) → ℝ := fun x ↦ ∫ w, |∑ j, v j * w j| *
      ∫ w', |∑ j, v j * w' j| * (D * ‖h‖ * Θ (x + S₀ *ᵥ w + S₀ *ᵥ w')) ∂γ ∂γ with hMx
  have hD3 : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |dirDeriv h (dirDeriv h (dirDeriv h F)) (x + t • h)| ≤ Mx x := by
    intro x t ht
    rw [hF_def, dirDeriv_three_eq hφ S₀ hv]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (ae_of_all _ fun _ ↦ abs_nonneg _) (houter_int x) (ae_of_all _ fun w ↦ ?_))
    show |(∑ j, v j * w j) * ∫ w', (∑ j, v j * w' j) *
        gaussSmooth (dirDeriv h φ) S₀ (x + t • h + S₀ *ᵥ w + S₀ *ᵥ w') ∂γ| ≤ _
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (ae_of_all _ fun _ ↦ abs_nonneg _) (hinner_int x w) (ae_of_all _ fun w' ↦ ?_))
    show |(∑ j, v j * w' j) * gaussSmooth (dirDeriv h φ) S₀ (x + t • h + S₀ *ᵥ w + S₀ *ᵥ w')| ≤
      |∑ j, v j * w' j| * (D * ‖h‖ * Θ (x + S₀ *ᵥ w + S₀ *ᵥ w'))
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [show x + t • h + S₀ *ᵥ w + S₀ *ᵥ w' = (x + S₀ *ᵥ w + S₀ *ᵥ w') + t • h by abel]
    exact hΨ _ t ht
  have hrem : ∀ x, |taylorRem F x h| ≤ Mx x / 6 := fun x ↦
    abs_taylorRem_le_of_dirDeriv hF x h (hD3 x)
  -- anti-concentration inside
  have hσ1 : 0 ≤ σ₁ := by
    refine le_trans ?_ (hσ δ₁ hδ₁0 0)
    exact Stein.pexp_nonneg hp0 fun ω ↦ integral_nonneg fun w ↦
      Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hΘσ : ∀ w w', Stein.pexp p (fun ω ↦ Θ (P ω + S₀ *ᵥ w + S₀ *ᵥ w')) ≤ σ₁ := by
    intro w w'
    refine le_trans (Stein.pexp_mono hp0 fun ω ↦ ?_) (hσ δ₁ hδ₁0 (S₀ *ᵥ w + S₀ *ᵥ w'))
    show ∫ w₃, χ (P ω + S₀ *ᵥ w + S₀ *ᵥ w' + S₀ *ᵥ w₃) ∂γ ≤ _
    refine integral_mono (integrable_of_continuous_mem_Icc (hχc.comp
      (continuous_const.add hS₀c)) (fun w₃ ↦ hχ01 _)) ?_ (fun w₃ ↦ ?_)
    · have := integrable_indicator_affine (measurableSet_shellSet δ₁ K) S₀
        (P ω + (S₀ *ᵥ w + S₀ *ᵥ w'))
      refine this.congr (ae_of_all _ fun w₃ ↦ ?_)
      simp only
      congr 1; abel
    · refine (hχle _).trans (le_of_eq ?_)
      congr 1; abel
  have hpM : Stein.pexp p (fun ω ↦ Mx (P ω)) ≤ D * ‖h‖ * σ₁ * E₁ ^ 2 := by
    simp only [hMx]
    rw [pexp_integral p _ fun ω ↦ houter_int (P ω)]
    calc ∫ w, Stein.pexp p (fun ω ↦ |∑ j, v j * w j| *
            ∫ w', |∑ j, v j * w' j| * (D * ‖h‖ * Θ (P ω + S₀ *ᵥ w + S₀ *ᵥ w')) ∂γ) ∂γ
        ≤ ∫ w, |∑ j, v j * w j| * (E₁ * (D * ‖h‖ * σ₁)) ∂γ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun w ↦ ?_)
            ((integrable_abs_sum_mul v).mul_const _) (ae_of_all _ fun w ↦ ?_)
          · exact Stein.pexp_nonneg hp0 fun ω ↦ mul_nonneg (abs_nonneg _)
              (integral_nonneg fun w' ↦ mul_nonneg (abs_nonneg _)
                (mul_nonneg hDh (hΘ01 _).1))
          beta_reduce
          rw [Stein.pexp_const_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [pexp_integral p _ fun ω ↦ hinner_int (P ω) w, ← integral_mul_const]
          refine integral_mono_of_nonneg (ae_of_all _ fun w' ↦ ?_)
            ((integrable_abs_sum_mul v).mul_const _) (ae_of_all _ fun w' ↦ ?_)
          · exact Stein.pexp_nonneg hp0 fun ω ↦ mul_nonneg (abs_nonneg _)
              (mul_nonneg hDh (hΘ01 _).1)
          show Stein.pexp p (fun ω ↦ |∑ j, v j * w' j| *
              (D * ‖h‖ * Θ (P ω + S₀ *ᵥ w + S₀ *ᵥ w'))) ≤ |∑ j, v j * w' j| * (D * ‖h‖ * σ₁)
          rw [Stein.pexp_const_mul, Stein.pexp_const_mul]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hΘσ w w') hDh)
            (abs_nonneg _)
      _ = D * ‖h‖ * σ₁ * E₁ ^ 2 := by
          rw [integral_mul_const]; ring
  have hE₁2 : E₁ ^ 2 ≤ ∑ j, v j ^ 2 := integral_abs_sum_mul_sq_le v
  calc Stein.pexp p (fun ω ↦ |taylorRem F (P ω) h|)
      ≤ Stein.pexp p (fun ω ↦ Mx (P ω) / 6) := Stein.pexp_mono hp0 fun ω ↦ hrem (P ω)
    _ = Stein.pexp p (fun ω ↦ Mx (P ω)) / 6 := by
        rw [show (fun ω ↦ Mx (P ω) / 6) = fun ω ↦ (1 / 6) * Mx (P ω) by funext; ring,
          Stein.pexp_const_mul]; ring
    _ ≤ D * ‖h‖ * σ₁ * E₁ ^ 2 / 6 := by gcongr
    _ ≤ D * ‖h‖ * σ₁ * (∑ j, v j ^ 2) / 6 := by
        gcongr
    _ = D * ‖h‖ * (∑ j, v j ^ 2) * (σ₀ + Csh * (ε + (‖h‖ + ε))) / 6 := by ring

end Mixed

/-! ## The three-fold split and the mixed hybrid step -/

/-- The scale `3^{-1/2}` of each third of the reservoir. -/
noncomputable def splitScale : ℝ := (√3)⁻¹

theorem splitScale_sq : splitScale ^ 2 = 1 / 3 := by
  rw [splitScale, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem splitScale_pos : 0 < splitScale := by unfold splitScale; positivity

theorem splitScale_le_one : splitScale ≤ 1 := by
  unfold splitScale
  rw [inv_le_one₀ (by positivity)]
  exact Real.one_le_sqrt.2 (by norm_num)

section ThreeSplit

variable {ι : Type*} {ι' : Type*} [Fintype ι']

/-- Gaussian smoothing as a three-fold smoothing by `3^{-1/2} R`. -/
theorem gaussSmooth_eq_three {φ : (ι → ℝ) → ℝ} (hφc : Continuous φ) {C : ℝ}
    (hφ : ∀ y, ‖φ y‖ ≤ C) (R : Matrix ι ι' ℝ) :
    gaussSmooth φ R = gaussSmooth (gaussSmooth (gaussSmooth φ (splitScale • R))
      (splitScale • R)) (splitScale • R) := by
  have ha := splitScale_sq
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hab1 : splitScale ^ 2 + (√2 * splitScale) ^ 2 = 1 := by
    rw [mul_pow, hs2, ha]; norm_num
  have hab2 : (√2)⁻¹ ^ 2 + (√2)⁻¹ ^ 2 = 1 := by
    rw [inv_pow, hs2]; norm_num
  have hnum : (√2)⁻¹ * (√2 * splitScale) = splitScale := by
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  rw [gaussSmooth_eq_gaussSmooth_gaussSmooth hφc hφ R hab1,
    gaussSmooth_eq_gaussSmooth_gaussSmooth hφc hφ ((√2 * splitScale) • R) hab2, smul_smul,
    hnum]

end ThreeSplit

section StepB

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*} [∀ i, Fintype (X i)]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **The mixed hybrid step.** At step `k`, with a reservoir of Euclidean covariance `≥ v₀ I` and
shell probabilities of the prefix plus a third of the reservoir bounded by `σ₀ + Csh δ`, a
sandwich-type test whose derivative (bounded by `D`) lives in the `ε`-shell satisfies
`|E φ(H_{k+1}) − E φ(H_k)| ≤ D (3 S²/v₀)/6 · ((σ₀ + Csh (2ε + b)) A₃ b³ + Csh (S√S b)⁴ E‖Z‖⁴)`. -/
theorem abs_hexp_succ_sub_le_mixed {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) (L : κ → Matrix ι ι ℝ)
    (hmean : ∀ i a, ∑ x, p i x * Y i x a = 0)
    (hcov : ∀ i a b, ∑ x, p i x * (Y i x a * Y i x b) = (L i * (L i)ᵀ) a b)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ i x, ‖Y i x‖ ≤ b)
    {φ : (ι → ℝ) → ℝ} (hφ : SmoothBdd φ) (h01 : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    {K : Set (ι → ℝ)} {ε D : ℝ} (hε : 0 < ε) (hD : ∀ y, ‖fderiv ℝ φ y‖ ≤ D)
    (hsupp : ∀ y ∉ shellSet ε K, fderiv ℝ φ y = 0) {k : ℕ} (hk : k < n) {v₀ : ℝ} (hv0 : 0 < v₀)
    (hv : ∀ u : ι → ℝ, v₀ * (u ⬝ᵥ u) ≤
      u ⬝ᵥ ((twinMat L (resSet e k) * (twinMat L (resSet e k))ᵀ) *ᵥ u))
    {σ₀ Csh : ℝ} (hCsh : 0 ≤ Csh)
    (hσ : ∀ δ, 0 ≤ δ → ∀ u : ι → ℝ, Stein.pexp p (fun ω ↦ ∫ w,
      (shellSet δ K).indicator (fun _ ↦ (1 : ℝ))
        (prefixSum e Y k ω + (splitScale • twinMat L (resSet e k)) *ᵥ w + u)
          ∂stdGaussianPi (κ × ι)) ≤ σ₀ + Csh * δ) :
    |hexp p e Y L φ (k + 1) - hexp p e Y L φ k| ≤
      D * (3 * (Fintype.card ι : ℝ) ^ 2 / v₀) / 6 *
        ((σ₀ + Csh * (2 * ε + b)) * (lindebergMomentConst ι * b ^ 3) +
          Csh * (((Fintype.card ι : ℝ) * √(Fintype.card ι : ℝ) * b) ^ 4 *
            gaussFourthMoment ι)) := by
  set i := e ⟨k, hk⟩ with hi
  set R := twinMat L (resSet e k) with hR
  set S₀ := splitScale • R with hS₀
  set P := prefixSum e Y k with hP
  set ν := stdGaussianPi ι
  set S : ℝ := (Fintype.card ι : ℝ) with hS
  have hφb : ∀ y, ‖φ y‖ ≤ 1 := norm_le_one_of_mem_Icc h01
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  set F := gaussSmooth φ R with hF_def
  have hF3 : F = gaussSmooth (gaussSmooth (gaussSmooth φ S₀) S₀) S₀ :=
    gaussSmooth_eq_three hφ.continuous hφb R
  have hFc : Continuous F := continuous_gaussSmooth hφ.continuous hφb R
  have hF0 : ∀ x, |F x| ≤ 1 := fun x ↦ by
    rw [← Real.norm_eq_abs]; exact norm_gaussSmooth_le hφb R x
  -- the quadratic lower bound for `S₀`
  have hv' : ∀ u : ι → ℝ, v₀ / 3 * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((S₀ * S₀ᵀ) *ᵥ u) := by
    refine quadForm_sup_of_euclid (by positivity) fun u ↦ ?_
    have hSS : S₀ * S₀ᵀ = (splitScale ^ 2) • (R * Rᵀ) := by
      rw [hS₀, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
    rw [hSS, Matrix.smul_mulVec, dotProduct_smul, splitScale_sq, smul_eq_mul]
    have := hv u
    linarith
  have hσnn : ∀ δ, 0 ≤ δ → 0 ≤ σ₀ + Csh * δ := fun δ hδ ↦
    le_trans (Stein.pexp_nonneg hp0 fun ω ↦ integral_nonneg fun w ↦
      Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _) (hσ δ hδ 0)
  set C' := D * (3 * S ^ 2 / v₀) / 6 with hC'
  have hC'0 : 0 ≤ C' := by positivity
  -- the per-direction bound
  have hq : ∀ h : ι → ℝ, Stein.pexp p (fun ω ↦ |taylorRem F (P ω) h|) ≤
      C' * (‖h‖ ^ 3 * (σ₀ + Csh * (2 * ε)) + Csh * ‖h‖ ^ 4) := by
    intro h
    obtain ⟨v, hvh, hv2⟩ := exists_mulVec_eq_of_quadForm_ge (by positivity : 0 < v₀ / 3) hv' h
    have hσ' : ∀ δ, 0 ≤ δ → ∀ u : ι → ℝ, Stein.pexp p (fun ω ↦ ∫ w,
        (shellSet δ K).indicator (fun _ ↦ (1 : ℝ)) (P ω + S₀ *ᵥ w + u)
          ∂stdGaussianPi (κ × ι)) ≤ σ₀ + Csh * δ := hσ
    have h1 := pexp_abs_taylorRem_le hp0 P S₀ hφ hε hD hsupp hσ' hvh
    rw [← hF3] at h1
    have hr2 : ((S / √(v₀ / 3)) ^ 2) = 3 * S ^ 2 / v₀ := by
      rw [div_pow, Real.sq_sqrt (by positivity)]; field_simp
    rw [hr2] at hv2
    have hnn := hσnn (ε + (‖h‖ + ε)) (by positivity)
    refine h1.trans ?_
    calc D * ‖h‖ * (∑ j, v j ^ 2) * (σ₀ + Csh * (ε + (‖h‖ + ε))) / 6
        ≤ D * ‖h‖ * (3 * S ^ 2 / v₀ * ‖h‖ ^ 2) * (σ₀ + Csh * (ε + (‖h‖ + ε))) / 6 := by
          gcongr
      _ = C' * (‖h‖ ^ 3 * (σ₀ + Csh * (2 * ε)) + Csh * ‖h‖ ^ 4) := by
          rw [hC']; ring
  -- the swap as a difference of Taylor remainders
  have hsw := fun ω ↦ sum_sub_integral_eq_taylorRem (hp1 i) (hmean i) (hcov i) hFc hF0 (P ω)
  rw [hexp_succ_eq hp1 e Y L φ hk, hexp_eq_integral_block p e Y L hφ.continuous h01 hk,
    ← Stein.pexp_sub]
  have heq : ∀ ω, (∑ y, p i y * ∫ w, φ (P ω + Y i y + R *ᵥ w) ∂stdGaussianPi (κ × ι)) -
      ∫ z, ∫ w, φ (P ω + L i *ᵥ z + R *ᵥ w) ∂stdGaussianPi (κ × ι) ∂ν =
      ∑ y, p i y * taylorRem F (P ω) (Y i y) - ∫ z, taylorRem F (P ω) (L i *ᵥ z) ∂ν :=
    fun ω ↦ (hsw ω).1
  refine le_trans (le_of_eq (congrArg abs (congrArg (Stein.pexp p) (funext heq)))) ?_
  have hRint : ∀ ω, Integrable (fun z ↦ |taylorRem F (P ω) (L i *ᵥ z)|) ν :=
    fun ω ↦ (hsw ω).2.abs
  -- move the absolute value inside
  have hstep1 : |Stein.pexp p (fun ω ↦ ∑ y, p i y * taylorRem F (P ω) (Y i y) -
      ∫ z, taylorRem F (P ω) (L i *ᵥ z) ∂ν)| ≤
      ∑ y, p i y * Stein.pexp p (fun ω ↦ |taylorRem F (P ω) (Y i y)|) +
        ∫ z, Stein.pexp p (fun ω ↦ |taylorRem F (P ω) (L i *ᵥ z)|) ∂ν := by
    refine (Stein.abs_pexp_le hp0 _).trans ?_
    refine (Stein.pexp_mono hp0 fun ω ↦ (abs_sub _ _).trans (add_le_add
      ((Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun y _ ↦ by
        rw [abs_mul, abs_of_nonneg (hp0 i y)])))
      abs_integral_le_integral_abs)).trans (le_of_eq ?_)
    rw [Stein.pexp_add, Stein.pexp_sum, pexp_integral p _ hRint]
    congr 1
    exact Finset.sum_congr rfl fun y _ ↦ Stein.pexp_const_mul _ _ _
  refine hstep1.trans ?_
  -- data side
  have hdata : ∑ y, p i y * Stein.pexp p (fun ω ↦ |taylorRem F (P ω) (Y i y)|) ≤
      C' * ((σ₀ + Csh * (2 * ε + b)) * ∑ y, p i y * ‖Y i y‖ ^ 3) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ ↦ ?_
    refine (mul_le_mul_of_nonneg_left (hq (Y i y)) (hp0 i y)).trans ?_
    have hY := hb i y
    have hY0 := norm_nonneg (Y i y)
    have h4 : ‖Y i y‖ ^ 4 ≤ b * ‖Y i y‖ ^ 3 := by
      rw [pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_right hY (by positivity)
    have : ‖Y i y‖ ^ 3 * (σ₀ + Csh * (2 * ε)) + Csh * ‖Y i y‖ ^ 4 ≤
        (σ₀ + Csh * (2 * ε + b)) * ‖Y i y‖ ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left h4 hCsh]
    calc p i y * (C' * (‖Y i y‖ ^ 3 * (σ₀ + Csh * (2 * ε)) + Csh * ‖Y i y‖ ^ 4))
        ≤ p i y * (C' * ((σ₀ + Csh * (2 * ε + b)) * ‖Y i y‖ ^ 3)) := by
          gcongr; exact hp0 i y
      _ = C' * ((σ₀ + Csh * (2 * ε + b)) * (p i y * ‖Y i y‖ ^ 3)) := by ring
  -- Gaussian side
  have h3int := integrable_norm_mulVec_pow_three_stdGaussianPi (L i)
  obtain ⟨h4int, h4le⟩ := integral_norm_mulVec_pow_four_le (L i)
  have hgauss : ∫ z, Stein.pexp p (fun ω ↦ |taylorRem F (P ω) (L i *ᵥ z)|) ∂ν ≤
      C' * ((σ₀ + Csh * (2 * ε)) * ∫ z, ‖L i *ᵥ z‖ ^ 3 ∂ν +
        Csh * ∫ z, ‖L i *ᵥ z‖ ^ 4 ∂ν) := by
    have hI : Integrable (fun z ↦ C' * (‖L i *ᵥ z‖ ^ 3 * (σ₀ + Csh * (2 * ε)) +
        Csh * ‖L i *ᵥ z‖ ^ 4)) ν :=
      ((h3int.mul_const _).add (h4int.const_mul _)).const_mul _
    refine (integral_mono_of_nonneg (ae_of_all _ fun z ↦ Stein.pexp_nonneg hp0 fun ω ↦
      abs_nonneg _) hI (ae_of_all _ fun z ↦ hq _)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add (h3int.mul_const _) (h4int.const_mul _),
      integral_mul_const, integral_const_mul]
    ring
  have hA := sum_cube_add_integral_cube_le (hp0 i) (hp1 i) (hcov i) hb0 (hb i)
  have hm := matrixAbsSum_le_of_cov (hp0 i) (hp1 i) (hcov i) hb0 (hb i)
  have hm4 : matrixAbsSum (L i) ^ 4 ≤ (S * √S * b) ^ 4 :=
    pow_le_pow_left₀ (matrixAbsSum_nonneg _) hm 4
  have hM4 := gaussFourthMoment_nonneg (ι := ι)
  have hσb := hσnn (2 * ε + b) (by positivity)
  have hE3 : 0 ≤ ∫ z, ‖L i *ᵥ z‖ ^ 3 ∂ν := integral_nonneg fun _ ↦ by positivity
  have hY3 : 0 ≤ ∑ y, p i y * ‖Y i y‖ ^ 3 :=
    Finset.sum_nonneg fun y _ ↦ mul_nonneg (hp0 i y) (by positivity)
  have hmono : (σ₀ + Csh * (2 * ε)) ≤ σ₀ + Csh * (2 * ε + b) := by nlinarith
  calc _ ≤ C' * ((σ₀ + Csh * (2 * ε + b)) * ∑ y, p i y * ‖Y i y‖ ^ 3) +
        C' * ((σ₀ + Csh * (2 * ε)) * ∫ z, ‖L i *ᵥ z‖ ^ 3 ∂ν +
          Csh * ∫ z, ‖L i *ᵥ z‖ ^ 4 ∂ν) := add_le_add hdata hgauss
    _ ≤ C' * ((σ₀ + Csh * (2 * ε + b)) * (∑ y, p i y * ‖Y i y‖ ^ 3 +
          ∫ z, ‖L i *ᵥ z‖ ^ 3 ∂ν) + Csh * ((S * √S * b) ^ 4 * gaussFourthMoment ι)) := by
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hC'0
        have : Csh * ∫ z, ‖L i *ᵥ z‖ ^ 4 ∂ν ≤ Csh * ((S * √S * b) ^ 4 * gaussFourthMoment ι) :=
          mul_le_mul_of_nonneg_left (h4le.trans (mul_le_mul_of_nonneg_right hm4 hM4)) hCsh
        nlinarith [mul_le_mul_of_nonneg_right hmono hE3]
    _ ≤ C' * ((σ₀ + Csh * (2 * ε + b)) * (lindebergMomentConst ι * b ^ 3) +
          Csh * ((S * √S * b) ^ 4 * gaussFourthMoment ι)) := by
        gcongr

end StepB

/-! ## Pass 1 as a sum of step costs, and partial telescoping -/

/-- The pass-1 budget `A₃ B³/6 · (c₃ (2 + r₀) + 4 C_H (c √c)⁻¹)` (to be divided by `n^{1/4}`). -/
noncomputable def quarterBudget (ι : Type*) [Fintype ι] (c : ℝ) (r₀ : ℕ) (B : ℝ) : ℝ :=
  lindebergMomentConst ι * B ^ 3 / 6 *
    (ConvexSmoothIndicator.sandwichConst ι 3 * (2 + r₀) +
      4 * reservoirHermiteConst ι * (c * √c)⁻¹)

section PassOne

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*} [∀ i, Fintype (X i)]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **Pass 1, step costs.** Under the pass-1 hypotheses, the step costs of a sandwich-type test
at scale `n^{-1/4}` sum to at most `quarterBudget / n^{1/4}`. -/
theorem sum_abs_hexp_sub_le_quarter {p : ∀ i, X i → ℝ} {Y : ∀ i, X i → ι → ℝ}
    {L : κ → Matrix ι ι ℝ} (e : Fin n ≃ κ) (hn : 0 < n) (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) (hmean : ∀ i a, ∑ x, p i x * Y i x a = 0)
    (hcov : ∀ i a b, ∑ x, p i x * (Y i x a * Y i x b) = (L i * (L i)ᵀ) a b)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i x, ‖Y i x‖ ≤ B / √(n : ℝ))
    {c : ℝ} (hc : 0 < c) {r₀ : ℕ} (hres : ReservoirCond e L c r₀)
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (h01 : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    (hd : ∀ (k : ℕ) (x : ι → ℝ), ‖iteratedFDeriv ℝ k φ x‖ ≤
      ConvexSmoothIndicator.sandwichConst ι k / ((√√(n : ℝ))⁻¹) ^ k) :
    ∑ k ∈ Finset.range n, |hexp p e Y L φ (k + 1) - hexp p e Y L φ k| ≤
      quarterBudget ι c r₀ B / √√(n : ℝ) := by
  have hb0 : 0 ≤ B / √(n : ℝ) := by positivity
  rw [quarterBudget]
  refine sum_range_le_quarter hn r₀ (ConvexSmoothIndicator.sandwichConst_nonneg 3)
    (reservoirHermiteConst_nonneg ι) lindebergMomentConst_nonneg hB hc.le
    (a := fun k ↦ |hexp p e Y L φ (k + 1) - hexp p e Y L φ k|) ?_ ?_
  · intro k hk hJ
    have hceil : 0 < ⌈√(n : ℝ)⌉₊ := Nat.ceil_pos.2 (Real.sqrt_pos.2 (by exact_mod_cast hn))
    have hj : 0 < n - 1 - k := by omega
    have hv0 : 0 < c * ((n - 1 - k : ℕ) : ℝ) / n := by
      have : (0 : ℝ) < ((n - 1 - k : ℕ) : ℝ) := by exact_mod_cast hj
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have hv := reservoir_quadForm hres hk (by omega)
    refine abs_hexp_succ_sub_le hp0 hp1 e Y L hφ.continuous h01 hk fun U ↦ ?_
    refine (abs_step_le_of_reservoir (hp0 _) (hp1 _) (hmean _) (hcov _) hb0 (hb _) hφ h01
      (fun j ↦ ⟨_, hd j⟩) _ hv0 hv U).trans (le_of_eq ?_)
    have := reservoir_step_const_eq (B := B) hc hn hj
    unfold reservoirHermiteConst
    calc gaussDerivConst 3 * (Fintype.card ι : ℝ) ^ 3 *
            ((c * ((n - 1 - k : ℕ) : ℝ) / n) * √(c * ((n - 1 - k : ℕ) : ℝ) / n))⁻¹ / 6 *
          (lindebergMomentConst ι * (B / √(n : ℝ)) ^ 3)
        = gaussDerivConst 3 * (Fintype.card ι : ℝ) ^ 3 / 6 * lindebergMomentConst ι *
          (((c * ((n - 1 - k : ℕ) : ℝ) / n) * √(c * ((n - 1 - k : ℕ) : ℝ) / n))⁻¹ *
            (B / √(n : ℝ)) ^ 3) := by ring
      _ = _ := by rw [this]; ring
  · intro k hk _
    refine abs_hexp_succ_sub_le hp0 hp1 e Y L hφ.continuous h01 hk fun U ↦ ?_
    refine (abs_step_le_of_sandwich (hp0 _) (hp1 _) (hmean _) (hcov _) hb0 (hb _) hφ h01 hd
      _ U).trans (le_of_eq ?_)
    rw [inv_pow, div_inv_eq_mul]
    ring

/-- **Pass 1, partial telescoping.** Every intermediate hybrid `H_{k'}` (`k' ≤ n`) is within
`quarterBudget / n^{1/4}` of the twin law on sandwich-type tests at scale `n^{-1/4}`. -/
theorem abs_hexp_sub_twinLaw_le_quarter {p : ∀ i, X i → ℝ} {Y : ∀ i, X i → ι → ℝ}
    {L : κ → Matrix ι ι ℝ} (e : Fin n ≃ κ) (hn : 0 < n) (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) (hmean : ∀ i a, ∑ x, p i x * Y i x a = 0)
    (hcov : ∀ i a b, ∑ x, p i x * (Y i x a * Y i x b) = (L i * (L i)ᵀ) a b)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i x, ‖Y i x‖ ≤ B / √(n : ℝ))
    {c : ℝ} (hc : 0 < c) {r₀ : ℕ} (hres : ReservoirCond e L c r₀)
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (h01 : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    (hd : ∀ (k : ℕ) (x : ι → ℝ), ‖iteratedFDeriv ℝ k φ x‖ ≤
      ConvexSmoothIndicator.sandwichConst ι k / ((√√(n : ℝ))⁻¹) ^ k) {k' : ℕ} (hk' : k' ≤ n) :
    |hexp p e Y L φ k' - ∫ y, φ y ∂(twinLaw L)| ≤ quarterBudget ι c r₀ B / √√(n : ℝ) := by
  rw [← hexp_zero hp1 e Y L hφ.continuous, ← Finset.sum_range_sub (fun k ↦ hexp p e Y L φ k)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_
    (sum_abs_hexp_sub_le_quarter e hn hp0 hp1 hmean hcov hB hb hc hres hφ h01 hd))
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk')
    fun _ _ _ ↦ abs_nonneg _

end PassOne

/-! ## Quadratic forms of covariance factors -/

section Quad

variable {ι : Type*} [Fintype ι] {X : Type*} [Fintype X]

theorem quadForm_mul_transpose_nonneg (L : Matrix ι ι ℝ) (u : ι → ℝ) :
    0 ≤ u ⬝ᵥ ((L * Lᵀ) *ᵥ u) := by
  have : u ⬝ᵥ ((L * Lᵀ) *ᵥ u) = (Lᵀ *ᵥ u) ⬝ᵥ (Lᵀ *ᵥ u) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  rw [this]
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _

/-- A covariance factor of a summand bounded by `b` has `uᵀ L Lᵀ u ≤ |ι| b² (u ⬝ u)`. -/
theorem quadForm_le_of_cov {p : X → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {Y : X → ι → ℝ} {L : Matrix ι ι ℝ}
    (hY2 : ∀ a b, ∑ x, p x * (Y x a * Y x b) = (L * Lᵀ) a b) {b : ℝ}
    (hb : ∀ x, ‖Y x‖ ≤ b) (u : ι → ℝ) :
    u ⬝ᵥ ((L * Lᵀ) *ᵥ u) ≤ (Fintype.card ι : ℝ) * b ^ 2 * (u ⬝ᵥ u) := by
  have key : u ⬝ᵥ ((L * Lᵀ) *ᵥ u) = ∑ x, p x * (∑ a, u a * Y x a) ^ 2 := by
    calc u ⬝ᵥ ((L * Lᵀ) *ᵥ u) = ∑ a, ∑ b', u a * ((L * Lᵀ) a b' * u b') := by
          simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      _ = ∑ a, ∑ b', ∑ x, p x * ((u a * Y x a) * (u b' * Y x b')) := by
          refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b' _ ↦ ?_
          rw [← hY2, Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ ↦ by ring
      _ = ∑ a, ∑ x, ∑ b', p x * ((u a * Y x a) * (u b' * Y x b')) :=
          Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
      _ = ∑ x, ∑ a, ∑ b', p x * ((u a * Y x a) * (u b' * Y x b')) := Finset.sum_comm
      _ = ∑ x, p x * (∑ a, u a * Y x a) ^ 2 := by
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ ↦ by rw [Finset.mul_sum]
  rw [key]
  have hpt : ∀ x, (∑ a, u a * Y x a) ^ 2 ≤ (Fintype.card ι : ℝ) * b ^ 2 * (u ⬝ᵥ u) := by
    intro x
    have hcs2 : (∑ a, u a * Y x a) ^ 2 ≤ (∑ a, u a ^ 2) * ∑ a, Y x a ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hY : ∑ a, Y x a ^ 2 ≤ (Fintype.card ι : ℝ) * b ^ 2 := by
      calc ∑ a, Y x a ^ 2 ≤ ∑ _a : ι, b ^ 2 := Finset.sum_le_sum fun a _ ↦ by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) ((abs_apply_le_norm _ a).trans (hb x)) 2
        _ = _ := by simp
    have huu : ∑ a, u a ^ 2 = u ⬝ᵥ u := by simp [dotProduct, sq]
    rw [huu] at hcs2
    have hu0 : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
    nlinarith
  calc ∑ x, p x * (∑ a, u a * Y x a) ^ 2
      ≤ ∑ x, p x * ((Fintype.card ι : ℝ) * b ^ 2 * (u ⬝ᵥ u)) :=
        Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hpt x) (hp0 x)
    _ = _ := by rw [← Finset.sum_mul, hp1, one_mul]

end Quad

/-! ## The modified family for the anti-concentration bound -/

section Modified

variable {κ : Type*} [Fintype κ] {X : κ → Type*} [∀ i, Fintype (X i)]
  {ι : Type*} [Fintype ι] {n : ℕ}

/-- Summands of the modified family at step `k`: the index `e k` is removed (`0`), indices swapped
after `k` are scaled by `a`. -/
noncomputable def acY (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) (k : ℕ) (a : ℝ) :
    ∀ i, X i → ι → ℝ :=
  fun i x ↦ if (e.symm i : ℕ) = k then 0 else if (e.symm i : ℕ) < k then Y i x else a • Y i x

/-- Covariance factors of the modified family. -/
noncomputable def acL (e : Fin n ≃ κ) (L : κ → Matrix ι ι ℝ) (k : ℕ) (a : ℝ) :
    κ → Matrix ι ι ℝ :=
  fun i ↦ if (e.symm i : ℕ) = k then 0 else if (e.symm i : ℕ) < k then L i else a • L i

omit [Fintype κ] [∀ i, Fintype (X i)] [Fintype ι] in
theorem prefixSum_acY (e : Fin n ≃ κ) (Y : ∀ i, X i → ι → ℝ) (k : ℕ) (a : ℝ)
    (ω : ∀ i, X i) : prefixSum e (acY e Y k a) (k + 1) ω = prefixSum e Y k ω := by
  unfold prefixSum
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp only [acY, Equiv.symm_apply_apply]
  by_cases h1 : (m : ℕ) = k
  · simp [h1]
  · by_cases h2 : (m : ℕ) < k
    · simp [h1, h2, show (m : ℕ) < k + 1 by omega]
    · simp [h2, show ¬ (m : ℕ) < k + 1 by omega]

omit [Fintype κ] [Fintype ι] in
theorem twinMat_acL_resSet [DecidableEq κ] (e : Fin n ≃ κ) (L : κ → Matrix ι ι ℝ) (k : ℕ) (a : ℝ) :
    twinMat (acL e L k a) (resSet e k) = a • twinMat L (resSet e k) := by
  ext r c
  simp only [twinMat_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hc : c.1 ∈ resSet e k
  · rw [if_pos hc, if_pos hc]
    obtain ⟨m, hm, hmc⟩ := Finset.mem_map.1 hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    have hs : (e.symm c.1 : ℕ) = m := by rw [← hmc]; simp
    simp only [acL, hs, show (m : ℕ) ≠ k by omega, show ¬ (m : ℕ) < k by omega, if_false,
      Matrix.smul_apply, smul_eq_mul]
  · rw [if_neg hc, if_neg hc, mul_zero]

omit [Fintype κ] [Fintype ι] in
theorem acY_mean (e : Fin n ≃ κ) {p : ∀ i, X i → ℝ} {Y : ∀ i, X i → ι → ℝ}
    (hmean : ∀ i a, ∑ x, p i x * Y i x a = 0) (k : ℕ) (a : ℝ) :
    ∀ i b, ∑ x, p i x * acY e Y k a i x b = 0 := by
  intro i b
  simp only [acY]
  split_ifs
  · simp
  · exact hmean i b
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ x, p i x * (a * Y i x b)) = a * ∑ x, p i x * Y i x b by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ ↦ by ring, hmean, mul_zero]

omit [Fintype κ] in
theorem acY_cov (e : Fin n ≃ κ) {p : ∀ i, X i → ℝ} {Y : ∀ i, X i → ι → ℝ}
    {L : κ → Matrix ι ι ℝ}
    (hcov : ∀ i a b, ∑ x, p i x * (Y i x a * Y i x b) = (L i * (L i)ᵀ) a b) (k : ℕ) (a : ℝ) :
    ∀ i r s, ∑ x, p i x * (acY e Y k a i x r * acY e Y k a i x s) =
      (acL e L k a i * (acL e L k a i)ᵀ) r s := by
  intro i r s
  simp only [acY, acL]
  split_ifs
  · simp
  · exact hcov i r s
  · simp only [Pi.smul_apply, smul_eq_mul, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_apply]
    rw [← hcov i r s, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring

omit [Fintype κ] [∀ i, Fintype (X i)] in
theorem acY_bound (e : Fin n ≃ κ) {Y : ∀ i, X i → ι → ℝ} {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ i x, ‖Y i x‖ ≤ b) (k : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ i x, ‖acY e Y k a i x‖ ≤ b := by
  intro i x
  simp only [acY]
  split_ifs
  · simpa using hb0
  · exact hb i x
  · rw [norm_smul, Real.norm_of_nonneg ha0]
    exact (mul_le_of_le_one_left (norm_nonneg _) ha1).trans (hb i x)

omit [Fintype κ] in
/-- The modified family satisfies the reservoir condition with `c' = a² c / 2` and
`r₀' = max r₀ ⌈2 |ι| B² / c⌉`. -/
theorem reservoirCond_acL {e : Fin n ≃ κ} {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {Y : ∀ i, X i → ι → ℝ} {L : κ → Matrix ι ι ℝ}
    (hcov : ∀ i a b, ∑ x, p i x * (Y i x a * Y i x b) = (L i * (L i)ᵀ) a b)
    {B : ℝ} (hb : ∀ i x, ‖Y i x‖ ≤ B / √(n : ℝ)) {c : ℝ} (hc : 0 < c) {r₀ : ℕ}
    (hres : ReservoirCond e L c r₀) {k : ℕ} (hk : k < n) {a : ℝ} (ha1 : a ^ 2 ≤ 1) :
    ReservoirCond e (acL e L k a) (a ^ 2 * c / 2)
      (max r₀ ⌈2 * (Fintype.card ι : ℝ) * B ^ 2 / c⌉₊) := by
  intro r hr hrn u
  have hn : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : r₀ ≤ r := le_trans (le_max_left _ _) hr
  have hrB : 2 * (Fintype.card ι : ℝ) * B ^ 2 / c ≤ r :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hr)
  have h1 := hres r hr0 hrn u
  set F := Finset.univ.filter (fun m : Fin n ↦ n - r ≤ (m : ℕ))
  set q : Fin n → ℝ := fun m ↦ u ⬝ᵥ ((L (e m) * (L (e m))ᵀ) *ᵥ u)
  set m₀ : Fin n := ⟨k, hk⟩
  have hq0 : ∀ m, 0 ≤ q m := fun m ↦ quadForm_mul_transpose_nonneg _ u
  have hpt : ∀ m, a ^ 2 * q m - (if m = m₀ then a ^ 2 * q m else 0) ≤
      u ⬝ᵥ ((acL e L k a (e m) * (acL e L k a (e m))ᵀ) *ᵥ u) := by
    intro m
    have hmk : (m = m₀) ↔ (m : ℕ) = k := by
      constructor
      · rintro rfl; rfl
      · intro h; exact Fin.ext h
    simp only [acL, Equiv.symm_apply_apply]
    by_cases h1 : (m : ℕ) = k
    · rw [if_pos h1, if_pos (hmk.2 h1)]
      simp
    · rw [if_neg h1, if_neg (fun h ↦ h1 (hmk.1 h)), sub_zero]
      by_cases h2 : (m : ℕ) < k
      · rw [if_pos h2]
        exact mul_le_of_le_one_left (hq0 m) ha1
      · rw [if_neg h2, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, sq]
  have hsum : ∑ m ∈ F, (if m = m₀ then a ^ 2 * q m else 0) ≤ a ^ 2 * q m₀ := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (sq_nonneg a) (hq0 m₀)
  have hqk : q m₀ ≤ (Fintype.card ι : ℝ) * (B / √(n : ℝ)) ^ 2 * (u ⬝ᵥ u) :=
    quadForm_le_of_cov (hp0 _) (hp1 _) (hcov _) (hb _) u
  rw [div_pow, Real.sq_sqrt hn'.le] at hqk
  have huu : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hmain : a ^ 2 * (c * r / n * (u ⬝ᵥ u)) - a ^ 2 * q m₀ ≤
      ∑ m ∈ F, u ⬝ᵥ ((acL e L k a (e m) * (acL e L k a (e m))ᵀ) *ᵥ u) := by
    calc a ^ 2 * (c * r / n * (u ⬝ᵥ u)) - a ^ 2 * q m₀
        ≤ a ^ 2 * ∑ m ∈ F, q m - ∑ m ∈ F, (if m = m₀ then a ^ 2 * q m else 0) := by
          have := mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
          linarith
      _ = ∑ m ∈ F, (a ^ 2 * q m - (if m = m₀ then a ^ 2 * q m else 0)) := by
          rw [Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum fun m _ ↦ hpt m
  refine le_trans ?_ hmain
  have hcr : 2 * (Fintype.card ι : ℝ) * B ^ 2 ≤ c * r := by
    rw [div_le_iff₀ hc] at hrB; linarith
  have ha0 : 0 ≤ a ^ 2 := sq_nonneg a
  have e1 : a ^ 2 * c / 2 * r / n * (u ⬝ᵥ u) =
      a ^ 2 * (c * r / 2) * (u ⬝ᵥ u) / n := by ring
  have e2 : a ^ 2 * (c * r / n * (u ⬝ᵥ u)) = a ^ 2 * (c * r) * (u ⬝ᵥ u) / n := by ring
  have hqk' : a ^ 2 * q m₀ ≤ a ^ 2 * ((Fintype.card ι : ℝ) * B ^ 2) * (u ⬝ᵥ u) / n := by
    have := mul_le_mul_of_nonneg_left hqk ha0
    calc a ^ 2 * q m₀ ≤ a ^ 2 * ((Fintype.card ι : ℝ) * (B ^ 2 / n) * (u ⬝ᵥ u)) := this
      _ = _ := by field_simp
  rw [e1, e2]
  have : a ^ 2 * (c * r / 2) * (u ⬝ᵥ u) / n + a ^ 2 * ((Fintype.card ι : ℝ) * B ^ 2) *
      (u ⬝ᵥ u) / n ≤ a ^ 2 * (c * r) * (u ⬝ᵥ u) / n := by
    rw [← add_div, div_le_div_iff_of_pos_right hn']
    have : (c * r / 2) + (Fintype.card ι : ℝ) * B ^ 2 ≤ c * r := by linarith
    have := mul_le_mul_of_nonneg_left this ha0
    nlinarith [mul_le_mul_of_nonneg_right this huu]
  linarith

end Modified

/-! ## Anti-concentration of a hybrid prefix plus a Gaussian -/

/-- `4 |ι|² (|ι| / √c) / √(2π)`: the convex-shell constant of a Gaussian with covariance `≥ c I`. -/
noncomputable def shellConst (ι : Type*) [Fintype ι] (c : ℝ) : ℝ :=
  4 * (Fintype.card ι : ℝ) ^ 2 * ((Fintype.card ι : ℝ) / √c) / √(2 * π)

theorem shellConst_nonneg (ι : Type*) [Fintype ι] (c : ℝ) : 0 ≤ shellConst ι c := by
  unfold shellConst; positivity

section AC

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*} [∀ i, Fintype (X i)]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **Translated twin-law shell bound.** Under `ReservoirCond` the translated `δ`-shell of a
convex set has twin-law mass `≤ shellConst ι c · δ`. -/
theorem twinLaw_preimage_add_shell_le {e : Fin n ≃ κ} {L : κ → Matrix ι ι ℝ} {c : ℝ} {r₀ : ℕ}
    (hres : ReservoirCond e L c r₀) (hr₀ : r₀ ≤ n) (hn : 0 < n) (hc : 0 < c)
    {K : Set (ι → ℝ)} (hK : Convex ℝ K) {δ : ℝ} (hδ : 0 ≤ δ) (u : ι → ℝ) :
    (twinLaw L).real ((fun y ↦ y + u) ⁻¹' shellSet δ K) ≤ shellConst ι c * δ := by
  set T := twinMat L Finset.univ
  have hpsd : (T * Tᵀ).PosSemidef := by
    have := Matrix.posSemidef_self_mul_conjTranspose T
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  obtain ⟨Q, hQ⟩ := exists_mul_transpose_eq_of_posSemidef hpsd
  have hlaw : twinLaw L = (stdGaussianPi ι).map (Q *ᵥ ·) :=
    map_mulVec_stdGaussianPi_eq T Q hQ.symm
  have hq : ∀ u : ι → ℝ, c * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((Q * Qᵀ) *ᵥ u) := by
    rw [hQ]
    exact quadForm_sup_of_euclid hc.le (total_quadForm hres hr₀ hn)
  have hsurj : Function.Surjective (Q *ᵥ ·) := fun h ↦
    let ⟨w, hw, _⟩ := exists_mulVec_eq_of_quadForm_ge hc hq h
    ⟨w, hw⟩
  have hdet : IsUnit Q.det :=
    (Matrix.isUnit_iff_isUnit_det Q).1 (Matrix.mulVec_surjective_iff_isUnit.1 hsurj)
  have hmeas : MeasurableSet ((fun y ↦ y + u) ⁻¹' shellSet δ K) :=
    (measurableSet_shellSet δ K).preimage (continuous_id.add continuous_const).measurable
  rw [hlaw, map_measureReal_apply (continuous_mulVec_const Q).measurable hmeas]
  have hpre : (fun z ↦ Q *ᵥ z) ⁻¹' ((fun y ↦ y + u) ⁻¹' shellSet δ K) =
      (fun z ↦ u + Q *ᵥ z) ⁻¹' shellSet δ K := by
    ext z; simp [add_comm]
  rw [hpre, ← map_measureReal_apply (continuous_const.add (continuous_mulVec_const Q)).measurable
    (measurableSet_shellSet δ K)]
  refine (map_affine_convexShell_le Q hdet u hK hδ).trans ?_
  have hinv := matrixMaxRowAbsSum_inv_le_of_quadForm hc hq hdet
  unfold shellConst
  have h4 : 0 ≤ 4 * (Fintype.card ι : ℝ) ^ 2 := by positivity
  calc 4 * (Fintype.card ι : ℝ) ^ 2 * matrixMaxRowAbsSum Q⁻¹ * δ / √(2 * π)
      ≤ 4 * (Fintype.card ι : ℝ) ^ 2 * ((Fintype.card ι : ℝ) / √c) * δ / √(2 * π) := by
        gcongr
    _ = _ := by ring

/-- **Anti-concentration of the hybrid prefix plus the reservoir scaled by `3^{-1/2}` (covariance one third).** For `n` beyond the
modified burn-in `max r₀ ⌈2|ι|B²/c⌉`, every shell of a convex set (translated by `u`) has
probability at most `shellConst ι (c/6) (δ + n^{-1/4}) + 2 quarterBudget / n^{1/4}` under
`prefixSum e Y k + 3^{-1/2} · twinMat L (resSet e k) · Z`. -/
theorem pexp_shell_prefix_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) (e : Fin n ≃ κ) (hn : 0 < n) {Y : ∀ i, X i → ι → ℝ}
    {L : κ → Matrix ι ι ℝ} (hmean : ∀ i a, ∑ x, p i x * Y i x a = 0)
    (hcov : ∀ i a b, ∑ x, p i x * (Y i x a * Y i x b) = (L i * (L i)ᵀ) a b)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i x, ‖Y i x‖ ≤ B / √(n : ℝ)) {c : ℝ} (hc : 0 < c) {r₀ : ℕ}
    (hres : ReservoirCond e L c r₀)
    (hN : max r₀ ⌈2 * (Fintype.card ι : ℝ) * B ^ 2 / c⌉₊ ≤ n) {k : ℕ} (hk : k < n)
    {K : Set (ι → ℝ)} (hK : Convex ℝ K) {δ : ℝ} (hδ : 0 ≤ δ) (u : ι → ℝ) :
    Stein.pexp p (fun ω ↦ ∫ w, (shellSet δ K).indicator (fun _ ↦ (1 : ℝ))
        (prefixSum e Y k ω + (splitScale • twinMat L (resSet e k)) *ᵥ w + u)
          ∂stdGaussianPi (κ × ι)) ≤
      shellConst ι (c / 6) * (δ + (√√(n : ℝ))⁻¹) +
        2 * (quarterBudget ι (c / 6) (max r₀ ⌈2 * (Fintype.card ι : ℝ) * B ^ 2 / c⌉₊) B /
          √√(n : ℝ)) := by
  set a := splitScale with ha
  set r₀' := max r₀ ⌈2 * (Fintype.card ι : ℝ) * B ^ 2 / c⌉₊ with hr₀'
  set γ := stdGaussianPi (κ × ι)
  set R := twinMat L (resSet e k) with hR
  set Δ := quarterBudget ι (c / 6) r₀' B / √√(n : ℝ) with hΔ
  have hc6 : a ^ 2 * c / 2 = c / 6 := by rw [ha, splitScale_sq]; ring
  have hres' : ReservoirCond e (acL e L k a) (c / 6) r₀' := by
    rw [← hc6]
    exact reservoirCond_acL hp0 hp1 hcov hb hc hres hk (by rw [ha, splitScale_sq]; norm_num)
  have hmean' := acY_mean e hmean k a
  have hcov' := acY_cov e hcov k a
  have hb' := acY_bound e (by positivity) hb k splitScale_pos.le splitScale_le_one
  have hc6p : 0 < c / 6 := by positivity
  have hε₀ : 0 < (√√(n : ℝ))⁻¹ :=
    inv_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 (by exact_mod_cast hn)))
  set ε₀ := (√√(n : ℝ))⁻¹ with hε₀_def
  set K₁ := cthickening δ K with hK₁
  set K₂ := (cthickening δ (interior K)ᶜ)ᶜ with hK₂
  obtain ⟨φu, hu_s, hu01, hu1, hu0, hud⟩ :=
    ConvexSmoothIndicator.exists_smooth_sandwich_upper K₁ hε₀
  obtain ⟨φl, hl_s, hl01, hl1, hl0, hld⟩ :=
    ConvexSmoothIndicator.exists_smooth_sandwich_lower K₂ hε₀
  set gu : (ι → ℝ) → ℝ := fun y ↦ φu (y + u) with hgu
  set gl : (ι → ℝ) → ℝ := fun y ↦ φl (y + u) with hgl
  have hgu_s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gu := hu_s.comp (contDiff_id.add contDiff_const)
  have hgl_s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gl := hl_s.comp (contDiff_id.add contDiff_const)
  have hgud : ∀ (j : ℕ) (y : ι → ℝ), ‖iteratedFDeriv ℝ j gu y‖ ≤
      ConvexSmoothIndicator.sandwichConst ι j / ε₀ ^ j := fun j y ↦ by
    rw [hgu, iteratedFDeriv_comp_add_right]; exact hud j _
  have hgld : ∀ (j : ℕ) (y : ι → ℝ), ‖iteratedFDeriv ℝ j gl y‖ ≤
      ConvexSmoothIndicator.sandwichConst ι j / ε₀ ^ j := fun j y ↦ by
    rw [hgl, iteratedFDeriv_comp_add_right]; exact hld j _
  have hk1 : k + 1 ≤ n := hk
  have hTu := abs_hexp_sub_twinLaw_le_quarter e hn hp0 hp1 hmean' hcov' hB hb' hc6p hres'
    hgu_s (fun y ↦ hu01 _) hgud hk1
  have hTl := abs_hexp_sub_twinLaw_le_quarter e hn hp0 hp1 hmean' hcov' hB hb' hc6p hres'
    hgl_s (fun y ↦ hl01 _) hgld hk1
  -- the modified hybrid at step `k + 1`
  have hhyb : ∀ f : (ι → ℝ) → ℝ, hexp p e (acY e Y k a) (acL e L k a) f (k + 1) =
      Stein.pexp p (fun ω ↦ ∫ w, f (prefixSum e Y k ω + (a • R) *ᵥ w) ∂γ) := by
    intro f
    unfold hexp hybrid
    rw [gaussSet_succ, twinMat_acL_resSet]
    simp only [prefixSum_acY]
    rfl
  -- pointwise sandwich of the shell indicator
  have hK₂K : K₂ ⊆ K₁ := fun x hx ↦ by
    have : x ∈ interior K := by
      by_contra hc'
      exact hx (self_subset_cthickening _ hc')
    exact self_subset_cthickening _ (interior_subset this)
  have hpt : ∀ y, (shellSet δ K).indicator (fun _ ↦ (1 : ℝ)) (y + u) ≤ gu y - gl y := by
    intro y
    by_cases hy : y + u ∈ shellSet δ K
    · rw [Set.indicator_of_mem hy]
      simp only [hgu, hgl, hu1 _ hy.1, hl0 _ (fun h ↦ h hy.2)]
      norm_num
    · rw [Set.indicator_of_notMem hy]
      simp only [hgu, hgl]
      by_cases h2 : y + u ∈ K₂
      · rw [hu1 _ (hK₂K h2)]; linarith [(hl01 (y + u)).2]
      · rw [hl0 _ h2]; linarith [(hu01 (y + u)).1]
  have hguc : Continuous gu := hgu_s.continuous
  have hglc : Continuous gl := hgl_s.continuous
  have hint : ∀ (g : (ι → ℝ) → ℝ), Continuous g → (∀ y, g y ∈ Set.Icc (0 : ℝ) 1) →
      ∀ ω, Integrable (fun w ↦ g (prefixSum e Y k ω + (a • R) *ᵥ w)) γ :=
    fun g hg h01 ω ↦ integrable_of_continuous_mem_Icc
      (hg.comp (continuous_const.add (continuous_mulVec_const _))) (fun w ↦ h01 _)
  have hstep1 : Stein.pexp p (fun ω ↦ ∫ w, (shellSet δ K).indicator (fun _ ↦ (1 : ℝ))
      (prefixSum e Y k ω + (a • R) *ᵥ w + u) ∂γ) ≤
      hexp p e (acY e Y k a) (acL e L k a) gu (k + 1) -
        hexp p e (acY e Y k a) (acL e L k a) gl (k + 1) := by
    rw [hhyb, hhyb, ← Stein.pexp_sub]
    refine Stein.pexp_mono hp0 fun ω ↦ ?_
    rw [← integral_sub (hint gu hguc (fun y ↦ hu01 _) ω) (hint gl hglc (fun y ↦ hl01 _) ω)]
    refine integral_mono_of_nonneg (ae_of_all _ fun w ↦
      Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
      ((hint gu hguc (fun y ↦ hu01 _) ω).sub (hint gl hglc (fun y ↦ hl01 _) ω))
      (ae_of_all _ fun w ↦ hpt _)
  -- the Gaussian side
  set tw := twinLaw (acL e L k a)
  have hr₀' : r₀' ≤ n := hN
  have hthick : IsOpen ((fun y ↦ y + u) ⁻¹' thickening ε₀ K₁) :=
    isOpen_thickening.preimage (continuous_id.add continuous_const)
  set M₂ := (cthickening ε₀ (interior K₂)ᶜ)ᶜ with hM₂
  have hM₂o : IsOpen ((fun y ↦ y + u) ⁻¹' M₂) :=
    isClosed_cthickening.isOpen_compl.preimage (continuous_id.add continuous_const)
  have hup : ∫ y, gu y ∂tw ≤ tw.real ((fun y ↦ y + u) ⁻¹' thickening ε₀ K₁) := by
    rw [← integral_indicator_one hthick.measurableSet]
    refine integral_mono (integrable_of_continuous_mem_Icc hguc (fun y ↦ hu01 _))
      ((integrable_const (1 : ℝ)).indicator hthick.measurableSet) fun y ↦ ?_
    by_cases h : y ∈ (fun y ↦ y + u) ⁻¹' thickening ε₀ K₁
    · rw [Set.indicator_of_mem h]; exact (hu01 _).2
    · rw [Set.indicator_of_notMem h]; exact le_of_eq (hu0 _ h)
  have hlo : tw.real ((fun y ↦ y + u) ⁻¹' M₂) ≤ ∫ y, gl y ∂tw := by
    rw [← integral_indicator_one hM₂o.measurableSet]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hM₂o.measurableSet)
      (integrable_of_continuous_mem_Icc hglc (fun y ↦ hl01 _)) fun y ↦ ?_
    by_cases h : y ∈ (fun y ↦ y + u) ⁻¹' M₂
    · rw [Set.indicator_of_mem h]
      exact le_of_eq (hl1 _ (closedBall_subset_of_mem_inner h)).symm
    · rw [Set.indicator_of_notMem h]; exact (hl01 _).1
  have hsub : thickening ε₀ K₁ ⊆ M₂ ∪ shellSet (ε₀ + δ) K := by
    intro x hx
    by_cases hxM : x ∈ M₂
    · exact Or.inl hxM
    · right
      have hx2 : x ∈ cthickening ε₀ (interior K₂)ᶜ := not_not.1 hxM
      rw [isClosed_cthickening.isOpen_compl.interior_eq, compl_compl] at hx2
      exact ⟨thickening_subset_cthickening _ _ (thickening_cthickening_subset ε₀ hδ _ hx),
        cthickening_cthickening_subset hε₀.le hδ _ hx2⟩
  have hsplit : tw.real ((fun y ↦ y + u) ⁻¹' thickening ε₀ K₁) ≤
      tw.real ((fun y ↦ y + u) ⁻¹' M₂) + tw.real ((fun y ↦ y + u) ⁻¹' shellSet (ε₀ + δ) K) := by
    refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
    rw [← Set.preimage_union]
    exact Set.preimage_mono hsub
  have hsh := twinLaw_preimage_add_shell_le hres' hr₀' hn hc6p hK (by positivity) u
    (δ := ε₀ + δ)
  have h1 := (abs_le.1 hTu).2
  have h2 := (abs_le.1 hTl).1
  calc _ ≤ hexp p e (acY e Y k a) (acL e L k a) gu (k + 1) -
        hexp p e (acY e Y k a) (acL e L k a) gl (k + 1) := hstep1
    _ ≤ (∫ y, gu y ∂tw + Δ) - (∫ y, gl y ∂tw - Δ) := by linarith
    _ ≤ shellConst ι (c / 6) * (ε₀ + δ) + 2 * Δ := by linarith
    _ = _ := by rw [add_comm ε₀ δ]

end AC

/-! ## Arithmetic -/

section Arith

/-- `∑_{1 ≤ j < n} 1/j ≤ 1 + log n`. -/
theorem sum_range_inv_le_one_add_log (n : ℕ) :
    ∑ j ∈ Finset.range n, (if 1 ≤ j then ((j : ℝ))⁻¹ else 0) ≤ 1 + Real.log n := by
  have hmono : ∑ j ∈ Finset.range n, (if 1 ≤ j then ((j : ℝ))⁻¹ else 0) ≤
      ∑ j ∈ Finset.range (n + 1), (if 1 ≤ j then ((j : ℝ))⁻¹ else 0) := by
    rw [Finset.sum_range_succ]
    have : 0 ≤ (if 1 ≤ n then ((n : ℝ))⁻¹ else 0) := by split_ifs <;> positivity
    linarith
  refine hmono.trans (le_of_eq_of_le ?_ (harmonic_le_one_add_log n))
  rw [Finset.sum_range_succ']
  simp only [show ¬ (1 ≤ 0) by omega, if_false, add_zero, le_add_iff_nonneg_left, zero_le,
    if_true, harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_succ]
  simp

/-- **Three-regime budget.** Step `k < n` with `j = n − 1 − k` costs `≤ Ac` if `j < J₀`,
`≤ Ab / j` if `J₀ ≤ j < J₁`, and `≤ Aa j^{-3/2}` if `J₀, J₁ ≤ j`. Then the total is
`≤ J₀ Ac + Ab (1 + log n) + 4 Aa / √(max J₀ J₁)`. -/
theorem sum_range_le_three {n J₀ J₁ : ℕ} (hJ₀ : 1 ≤ J₀) {a : ℕ → ℝ} {Ac Ab Aa : ℝ}
    (hAc : 0 ≤ Ac) (hAb : 0 ≤ Ab) (hAa : 0 ≤ Aa)
    (hc : ∀ k < n, n - 1 - k < J₀ → a k ≤ Ac)
    (hb : ∀ k < n, J₀ ≤ n - 1 - k → n - 1 - k < J₁ → a k ≤ Ab / ((n - 1 - k : ℕ) : ℝ))
    (ha : ∀ k < n, J₀ ≤ n - 1 - k → J₁ ≤ n - 1 - k →
      a k ≤ Aa * (((n - 1 - k : ℕ) : ℝ) * √((n - 1 - k : ℕ) : ℝ))⁻¹) :
    ∑ k ∈ Finset.range n, a k ≤
      J₀ * Ac + Ab * (1 + Real.log n) + 4 * Aa / √((max J₀ J₁ : ℕ) : ℝ) := by
  set M := max J₀ J₁ with hM
  have hM1 : 1 ≤ M := le_trans hJ₀ (le_max_left _ _)
  set g : ℕ → ℝ := fun j ↦ ((j : ℝ) * √(j : ℝ))⁻¹ with hg
  set F₁ : ℕ → ℝ := fun j ↦ if M ≤ j then Aa * g j else 0 with hF₁
  set F₂ : ℕ → ℝ := fun j ↦ if j < J₀ then Ac else 0 with hF₂
  set F₃ : ℕ → ℝ := fun j ↦ Ab * (if 1 ≤ j then ((j : ℝ))⁻¹ else 0) with hF₃
  have hF₁0 : ∀ j, 0 ≤ F₁ j := fun j ↦ by
    simp only [hF₁, hg]; split_ifs <;> positivity
  have hF₂0 : ∀ j, 0 ≤ F₂ j := fun j ↦ by simp only [hF₂]; split_ifs <;> positivity
  have hF₃0 : ∀ j, 0 ≤ F₃ j := fun j ↦ by simp only [hF₃]; split_ifs <;> positivity
  have hsplit : ∀ k ∈ Finset.range n, a k ≤ F₁ (n - 1 - k) + F₂ (n - 1 - k) + F₃ (n - 1 - k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases h0 : n - 1 - k < J₀
    · have := hc k hk h0
      have e2 : F₂ (n - 1 - k) = Ac := by simp only [hF₂, if_pos h0]
      linarith [hF₁0 (n - 1 - k), hF₃0 (n - 1 - k)]
    · push_neg at h0
      by_cases h1 : n - 1 - k < J₁
      · have := hb k hk h0 h1
        have e3 : F₃ (n - 1 - k) = Ab / ((n - 1 - k : ℕ) : ℝ) := by
          simp only [hF₃, if_pos (le_trans hJ₀ h0)]; rw [div_eq_mul_inv]
        linarith [hF₁0 (n - 1 - k), hF₂0 (n - 1 - k)]
      · push_neg at h1
        have := ha k hk h0 h1
        have e1 : F₁ (n - 1 - k) = Aa * g (n - 1 - k) := by
          simp only [hF₁]; rw [if_pos (show M ≤ n - 1 - k from max_le h0 h1)]
        linarith [hF₂0 (n - 1 - k), hF₃0 (n - 1 - k)]
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_range_reflect F₁ n,
    Finset.sum_range_reflect F₂ n, Finset.sum_range_reflect F₃ n]
  have h1 : ∑ j ∈ Finset.range n, F₁ j ≤ 4 * Aa / √(M : ℝ) := by
    have hfil : ∑ j ∈ Finset.range n, F₁ j = Aa * ∑ j ∈ Finset.Ico M n, g j := by
      rw [hF₁, ← Finset.sum_filter, Finset.mul_sum]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hfil, mul_comm 4 Aa, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (sum_Ico_inv_mul_sqrt_le hM1 n) hAa
  have h2 : ∑ j ∈ Finset.range n, F₂ j ≤ J₀ * Ac := by
    have hfil : ∑ j ∈ Finset.range n, F₂ j =
        ∑ j ∈ (Finset.range n).filter (fun j ↦ j < J₀), Ac := by
      rw [Finset.sum_filter]
    rw [hfil, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hAc
    have hsub : (Finset.range n).filter (fun j ↦ j < J₀) ⊆ Finset.range J₀ := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact hj.2
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    exact_mod_cast this
  have h3 : ∑ j ∈ Finset.range n, F₃ j ≤ Ab * (1 + Real.log n) := by
    rw [hF₃, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_range_inv_le_one_add_log n) hAb
  linarith

/-- The twelfth-root parametrization `s = n^{-1/12}`. -/
theorem twelfth_facts {n : ℕ} (hn : 0 < n) :
    let s := (n : ℝ) ^ (-(1 / 12 : ℝ))
    0 < s ∧ s ≤ 1 ∧ (n : ℝ) = (s ^ 12)⁻¹ ∧ √(n : ℝ) = (s ^ 6)⁻¹ ∧ √√(n : ℝ) = (s ^ 3)⁻¹ ∧
      (n : ℝ) ^ (-(1 / 3 : ℝ)) = s ^ 4 ∧ Real.log n ≤ 12 * s⁻¹ := by
  intro s
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : ∀ m : ℕ, s ^ m = (n : ℝ) ^ (-(m / 12 : ℝ)) := by
    intro m
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1; ring
  have hs0 : 0 < s := Real.rpow_pos_of_pos hn0 _
  refine ⟨hs0, Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpow, Real.rpow_neg hn0.le, inv_inv]; norm_num
  · rw [hpow, Real.rpow_neg hn0.le, inv_inv, Real.sqrt_eq_rpow]; norm_num
  · rw [hpow, Real.rpow_neg hn0.le, inv_inv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hn0.le]; norm_num
  · rw [hpow]; norm_num
  · have := Real.log_le_rpow_div hn0.le (by norm_num : (0 : ℝ) < 1 / 12)
    have hsi : s⁻¹ = (n : ℝ) ^ (1 / 12 : ℝ) := by
      show ((n : ℝ) ^ (-(1 / 12 : ℝ)))⁻¹ = _
      rw [Real.rpow_neg hn0.le, inv_inv]
    rw [hsi]
    linarith [show (n : ℝ) ^ (1 / 12 : ℝ) / (1 / 12) = 12 * (n : ℝ) ^ (1 / 12 : ℝ) by ring]

end Arith

/-! ## Constants -/

/-- Burn-in of the anti-concentration step: `max r₀ ⌈2 |ι| B² / c⌉`. -/
noncomputable def sharpBurnIn (ι : Type*) [Fintype ι] (c : ℝ) (r₀ : ℕ) (B : ℝ) : ℕ :=
  max r₀ ⌈2 * (Fintype.card ι : ℝ) * B ^ 2 / c⌉₊

/-- The constant of the mixed steps:
`c₁ S²/(2c) · ((Csh (3 + B) + 2 Q₀) A₃ B³ + Csh (S√S)⁴ B⁴ E‖Z‖⁴)`, with `Csh = shellConst ι (c/6)`
and `Q₀` the pass-1 budget of the modified family. -/
noncomputable def mixedConst (ι : Type*) [Fintype ι] (c : ℝ) (r₀ : ℕ) (B : ℝ) : ℝ :=
  ConvexSmoothIndicator.sandwichConst ι 1 * (Fintype.card ι : ℝ) ^ 2 / (2 * c) *
    ((shellConst ι (c / 6) * (3 + B) + 2 * quarterBudget ι (c / 6) (sharpBurnIn ι c r₀ B) B) *
        (lindebergMomentConst ι * B ^ 3) +
      shellConst ι (c / 6) * (((Fintype.card ι : ℝ) * √(Fintype.card ι : ℝ)) ^ 4 * B ^ 4 *
        gaussFourthMoment ι))

/-- The constant of the smooth-test comparison at `n^{-1/3}`. -/
noncomputable def thirdSmoothConst (ι : Type*) [Fintype ι] (c : ℝ) (r₀ : ℕ) (B : ℝ) : ℝ :=
  ((max r₀ 1 : ℕ) : ℝ) * (ConvexSmoothIndicator.sandwichConst ι 3 * lindebergMomentConst ι *
      B ^ 3 / 6) + 13 * mixedConst ι c r₀ B +
    4 * (reservoirHermiteConst ι * (c * √c)⁻¹ / 6 * lindebergMomentConst ι * B ^ 3)

/-- The constant of the pass-2 convex bound. -/
noncomputable def reservoirThirdConst (ι : Type*) [Fintype ι] (c : ℝ) (r₀ : ℕ) (B : ℝ) : ℝ :=
  shellConst ι c + thirdSmoothConst ι c r₀ B + (sharpBurnIn ι c r₀ B : ℝ) ^ (1 / 3 : ℝ)

theorem quarterBudget_nonneg (ι : Type*) [Fintype ι] {c : ℝ} (hc : 0 < c) (r₀ : ℕ) {B : ℝ}
    (hB : 0 ≤ B) : 0 ≤ quarterBudget ι c r₀ B := by
  unfold quarterBudget
  have := ConvexSmoothIndicator.sandwichConst_nonneg (ι := ι) 3
  have := reservoirHermiteConst_nonneg ι
  have := lindebergMomentConst_nonneg (ι := ι)
  positivity

theorem mixedConst_nonneg (ι : Type*) [Fintype ι] {c : ℝ} (hc : 0 < c) (r₀ : ℕ) {B : ℝ}
    (hB : 0 ≤ B) : 0 ≤ mixedConst ι c r₀ B := by
  unfold mixedConst
  have := ConvexSmoothIndicator.sandwichConst_nonneg (ι := ι) 1
  have := shellConst_nonneg ι (c / 6)
  have := quarterBudget_nonneg ι (by positivity : 0 < c / 6) (sharpBurnIn ι c r₀ B) hB
  have := lindebergMomentConst_nonneg (ι := ι)
  have := gaussFourthMoment_nonneg (ι := ι)
  positivity

theorem thirdSmoothConst_nonneg (ι : Type*) [Fintype ι] {c : ℝ} (hc : 0 < c) (r₀ : ℕ) {B : ℝ}
    (hB : 0 ≤ B) : 0 ≤ thirdSmoothConst ι c r₀ B := by
  unfold thirdSmoothConst
  have := ConvexSmoothIndicator.sandwichConst_nonneg (ι := ι) 3
  have := reservoirHermiteConst_nonneg ι
  have := lindebergMomentConst_nonneg (ι := ι)
  have := mixedConst_nonneg ι hc r₀ hB
  positivity

/-- The algebra of the mixed step in the `s = n^{-1/12}` parametrization. -/
theorem mixed_arith {s c₁ S c Csh Q₀ A₃ B T M₄ : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hc₁ : 0 ≤ c₁) (hc : 0 < c) (hCsh : 0 ≤ Csh) (hA₃ : 0 ≤ A₃)
    (hB : 0 ≤ B) (hM₄ : 0 ≤ M₄) :
    c₁ / (s ^ 4) ^ 1 * (3 * S ^ 2 * (s ^ 12)⁻¹ / c) / 6 *
        ((Csh * ((s ^ 3)⁻¹)⁻¹ + 2 * (Q₀ / (s ^ 3)⁻¹) + Csh * (2 * s ^ 4 + B / (s ^ 6)⁻¹)) *
            (A₃ * (B / (s ^ 6)⁻¹) ^ 3) +
          Csh * ((T * (B / (s ^ 6)⁻¹)) ^ 4 * M₄)) ≤
      c₁ * S ^ 2 / (2 * c) * ((Csh * (3 + B) + 2 * Q₀) * (A₃ * B ^ 3) +
        Csh * (T ^ 4 * B ^ 4 * M₄)) * s ^ 5 := by
  have e : c₁ / (s ^ 4) ^ 1 * (3 * S ^ 2 * (s ^ 12)⁻¹ / c) / 6 *
        ((Csh * ((s ^ 3)⁻¹)⁻¹ + 2 * (Q₀ / (s ^ 3)⁻¹) + Csh * (2 * s ^ 4 + B / (s ^ 6)⁻¹)) *
            (A₃ * (B / (s ^ 6)⁻¹) ^ 3) +
          Csh * ((T * (B / (s ^ 6)⁻¹)) ^ 4 * M₄)) =
      c₁ * S ^ 2 / (2 * c) * ((Csh + 2 * Q₀ + 2 * Csh * s + Csh * B * s ^ 3) * (A₃ * B ^ 3) *
        s ^ 5 + Csh * (T ^ 4 * B ^ 4 * M₄) * s ^ 8) := by
    field_simp
    ring
  rw [e]
  have hK : 0 ≤ c₁ * S ^ 2 / (2 * c) := by positivity
  have hs3 : s ^ 3 ≤ 1 := pow_le_one₀ hs0.le hs1
  have h1 : Csh + 2 * Q₀ + 2 * Csh * s + Csh * B * s ^ 3 ≤ Csh * (3 + B) + 2 * Q₀ := by
    nlinarith [mul_le_mul_of_nonneg_left hs1 hCsh, mul_le_mul_of_nonneg_left hs3
      (mul_nonneg hCsh hB)]
  have h8 : s ^ 8 ≤ s ^ 5 := pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
  have hX : 0 ≤ A₃ * B ^ 3 := by positivity
  have hY : 0 ≤ Csh * (T ^ 4 * B ^ 4 * M₄) := by positivity
  have hs5 : 0 ≤ s ^ 5 := by positivity
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hX) hs5
  have := mul_le_mul_of_nonneg_left h8 hY
  have hfin : (Csh + 2 * Q₀ + 2 * Csh * s + Csh * B * s ^ 3) * (A₃ * B ^ 3) * s ^ 5 +
      Csh * (T ^ 4 * B ^ 4 * M₄) * s ^ 8 ≤
      ((Csh * (3 + B) + 2 * Q₀) * (A₃ * B ^ 3) + Csh * (T ^ 4 * B ^ 4 * M₄)) * s ^ 5 := by
    nlinarith
  calc _ ≤ c₁ * S ^ 2 / (2 * c) *
        (((Csh * (3 + B) + 2 * Q₀) * (A₃ * B ^ 3) + Csh * (T ^ 4 * B ^ 4 * M₄)) * s ^ 5) :=
        mul_le_mul_of_nonneg_left hfin hK
    _ = _ := by ring

/-! ## Pass 2: smooth tests and convex sets -/

section Main

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*} [∀ i, Fintype (X i)]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **Pass 2, smooth tests.** Beyond the burn-in, every sandwich-type test at scale
`ε = n^{-1/3}` whose first derivative vanishes off the `ε`-shell of a convex `K` satisfies
`|E φ(∑ Y) − ∫ φ d twinLaw| ≤ thirdSmoothConst · n^{-1/3}`. -/
theorem abs_pexp_sub_twinLaw_le_smooth_third {p : ∀ i, X i → ℝ} {Y : ∀ i, X i → ι → ℝ}
    {L : κ → Matrix ι ι ℝ} (e : Fin n ≃ κ) (hn : 0 < n) (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) (hmean : ∀ i a, ∑ x, p i x * Y i x a = 0)
    (hcov : ∀ i a b, ∑ x, p i x * (Y i x a * Y i x b) = (L i * (L i)ᵀ) a b)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i x, ‖Y i x‖ ≤ B / √(n : ℝ))
    {c : ℝ} (hc : 0 < c) {r₀ : ℕ} (hres : ReservoirCond e L c r₀)
    (hN : sharpBurnIn ι c r₀ B ≤ n) {K : Set (ι → ℝ)} (hK : Convex ℝ K)
    {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (h01 : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    (hd : ∀ (k : ℕ) (x : ι → ℝ), ‖iteratedFDeriv ℝ k φ x‖ ≤
      ConvexSmoothIndicator.sandwichConst ι k / ((n : ℝ) ^ (-(1 / 3 : ℝ))) ^ k)
    (hsupp : ∀ x ∉ shellSet ((n : ℝ) ^ (-(1 / 3 : ℝ))) K, fderiv ℝ φ x = 0) :
    |Stein.pexp p (fun ω ↦ φ (∑ i, Y i (ω i))) - ∫ y, φ y ∂(twinLaw L)| ≤
      thirdSmoothConst ι c r₀ B * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨hs0, hs1, hnS, hsqrt, hqrt, hthird, hlog⟩ := twelfth_facts hn
  set s := (n : ℝ) ^ (-(1 / 12 : ℝ)) with hs
  rw [hthird] at hd hsupp ⊢
  have hb0 : 0 ≤ B / √(n : ℝ) := by positivity
  have hφB : SmoothBdd φ := ⟨hφ, fun k ↦ ⟨_, hd k⟩⟩
  have hD : ∀ y, ‖fderiv ℝ φ y‖ ≤ ConvexSmoothIndicator.sandwichConst ι 1 / (s ^ 4) ^ 1 :=
    fun y ↦ by rw [norm_fderiv_eq_norm_iteratedFDeriv_one]; exact hd 1 y
  have htel : Stein.pexp p (fun ω ↦ φ (∑ i, Y i (ω i))) - ∫ y, φ y ∂(twinLaw L) =
      ∑ k ∈ Finset.range n, (hexp p e Y L φ (k + 1) - hexp p e Y L φ k) := by
    rw [Finset.sum_range_sub (fun k ↦ hexp p e Y L φ k), hexp_n, hexp_zero hp1 e Y L hφ.continuous]
  rw [htel]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  set S : ℝ := (Fintype.card ι : ℝ) with hS
  set c₁ := ConvexSmoothIndicator.sandwichConst ι 1 with hc₁
  set c₃ := ConvexSmoothIndicator.sandwichConst ι 3 with hc₃
  set A₃ := lindebergMomentConst ι with hA₃
  set Csh := shellConst ι (c / 6) with hCsh
  set Q₀ := quarterBudget ι (c / 6) (sharpBurnIn ι c r₀ B) B with hQ₀
  set M₄ := gaussFourthMoment ι with hM₄
  have hc₁0 : 0 ≤ c₁ := ConvexSmoothIndicator.sandwichConst_nonneg 1
  have hc₃0 : 0 ≤ c₃ := ConvexSmoothIndicator.sandwichConst_nonneg 3
  have hA₃0 : 0 ≤ A₃ := lindebergMomentConst_nonneg
  have hCsh0 : 0 ≤ Csh := shellConst_nonneg ι (c / 6)
  have hQ₀0 : 0 ≤ Q₀ := quarterBudget_nonneg ι (by positivity) _ hB
  have hM₄0 : 0 ≤ M₄ := gaussFourthMoment_nonneg
  set σ₀ := Csh * (√√(n : ℝ))⁻¹ + 2 * (Q₀ / √√(n : ℝ)) with hσ₀
  set Ac := c₃ / (s ^ 4) ^ 3 / 6 * (A₃ * (B / √(n : ℝ)) ^ 3) with hAc
  set Ab := c₁ / (s ^ 4) ^ 1 * (3 * S ^ 2 * n / c) / 6 *
    ((σ₀ + Csh * (2 * s ^ 4 + B / √(n : ℝ))) * (A₃ * (B / √(n : ℝ)) ^ 3) +
      Csh * ((S * √S * (B / √(n : ℝ))) ^ 4 * M₄)) with hAb
  set Aa := reservoirHermiteConst ι * (c * √c)⁻¹ / 6 * A₃ * B ^ 3 with hAa
  have hAc0 : 0 ≤ Ac := by positivity
  have hAb0 : 0 ≤ Ab := by positivity
  have hAa0 : 0 ≤ Aa := by have := reservoirHermiteConst_nonneg ι; positivity
  set J₁ := ⌈(s ^ 8)⁻¹⌉₊ with hJ₁
  refine (sum_range_le_three (J₀ := max r₀ 1) (J₁ := J₁) (le_max_right _ _) hAc0 hAb0 hAa0
    ?_ ?_ ?_).trans ?_
  · -- unsmoothed steps
    intro k hk _
    refine abs_hexp_succ_sub_le hp0 hp1 e Y L hφ.continuous h01 hk fun U ↦ ?_
    exact abs_step_le_of_sandwich (hp0 _) (hp1 _) (hmean _) (hcov _) hb0 (hb _) hφ h01 hd _ U
  · -- mixed steps
    intro k hk h0 _
    have hj : 0 < n - 1 - k := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) h0)
    have hr : r₀ ≤ n - 1 - k := le_trans (le_max_left _ _) h0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hj' : (0 : ℝ) < ((n - 1 - k : ℕ) : ℝ) := by exact_mod_cast hj
    have hv0 : 0 < c * ((n - 1 - k : ℕ) : ℝ) / n := by positivity
    have hv := reservoir_quadForm hres hk hr
    have hσ : ∀ δ, 0 ≤ δ → ∀ u : ι → ℝ, Stein.pexp p (fun ω ↦ ∫ w,
        (shellSet δ K).indicator (fun _ ↦ (1 : ℝ))
          (prefixSum e Y k ω + (splitScale • twinMat L (resSet e k)) *ᵥ w + u)
            ∂stdGaussianPi (κ × ι)) ≤ σ₀ + Csh * δ := by
      intro δ hδ u
      refine (pexp_shell_prefix_le hp0 hp1 e hn hmean hcov hB hb hc hres hN hk hK hδ u).trans
        (le_of_eq ?_)
      rw [hσ₀, hCsh, hQ₀, sharpBurnIn]; ring
    refine (abs_hexp_succ_sub_le_mixed hp0 hp1 e Y L hmean hcov hb0 hb hφB h01
      (by positivity : (0 : ℝ) < s ^ 4) hD hsupp hk hv0 hv hCsh0 hσ).trans (le_of_eq ?_)
    rw [hAb, hS, hA₃, hM₄]
    field_simp
  · -- reservoir steps
    intro k hk h0 _
    have hj : 0 < n - 1 - k := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) h0)
    have hr : r₀ ≤ n - 1 - k := le_trans (le_max_left _ _) h0
    have hv0 : 0 < c * ((n - 1 - k : ℕ) : ℝ) / n := by
      have : (0 : ℝ) < ((n - 1 - k : ℕ) : ℝ) := by exact_mod_cast hj
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have hv := reservoir_quadForm hres hk hr
    refine abs_hexp_succ_sub_le hp0 hp1 e Y L hφ.continuous h01 hk fun U ↦ ?_
    refine (abs_step_le_of_reservoir (hp0 _) (hp1 _) (hmean _) (hcov _) hb0 (hb _) hφ h01
      (fun j ↦ ⟨_, hd j⟩) _ hv0 hv U).trans (le_of_eq ?_)
    have := reservoir_step_const_eq (B := B) hc hn hj
    rw [hAa, hA₃]
    unfold reservoirHermiteConst
    calc gaussDerivConst 3 * (Fintype.card ι : ℝ) ^ 3 *
            ((c * ((n - 1 - k : ℕ) : ℝ) / n) * √(c * ((n - 1 - k : ℕ) : ℝ) / n))⁻¹ / 6 *
          (lindebergMomentConst ι * (B / √(n : ℝ)) ^ 3)
        = gaussDerivConst 3 * (Fintype.card ι : ℝ) ^ 3 / 6 * lindebergMomentConst ι *
          (((c * ((n - 1 - k : ℕ) : ℝ) / n) * √(c * ((n - 1 - k : ℕ) : ℝ) / n))⁻¹ *
            (B / √(n : ℝ)) ^ 3) := by ring
      _ = _ := by rw [this]; ring
  · -- the arithmetic
    have hAcs : Ac ≤ c₃ * A₃ * B ^ 3 / 6 * s ^ 4 := by
      have e : Ac = c₃ * A₃ * B ^ 3 / 6 * s ^ 6 := by
        rw [hAc, hsqrt]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs0.le hs1 (by norm_num))
        (by positivity)
    have hAbs : Ab ≤ mixedConst ι c r₀ B * s ^ 5 := by
      have := mixed_arith (s := s) (c₁ := c₁) (S := S) (c := c) (Csh := Csh) (Q₀ := Q₀)
        (A₃ := A₃) (B := B) (T := S * √S) (M₄ := M₄) hs0 hs1 hc₁0 hc hCsh0 hA₃0 hB hM₄0
      have e : Ab = c₁ / (s ^ 4) ^ 1 * (3 * S ^ 2 * (s ^ 12)⁻¹ / c) / 6 *
        ((Csh * ((s ^ 3)⁻¹)⁻¹ + 2 * (Q₀ / (s ^ 3)⁻¹) + Csh * (2 * s ^ 4 + B / (s ^ 6)⁻¹)) *
            (A₃ * (B / (s ^ 6)⁻¹) ^ 3) +
          Csh * ((S * √S * (B / (s ^ 6)⁻¹)) ^ 4 * M₄)) := by
        rw [hAb, hσ₀, hqrt, hsqrt, hnS]
      rw [e]
      refine this.trans (le_of_eq ?_)
      rw [mixedConst, ← hc₁, ← hS, ← hCsh, ← hQ₀, ← hA₃, ← hM₄]
    have hlog' : 1 + Real.log n ≤ 13 * s⁻¹ := by
      have : 1 ≤ s⁻¹ := one_le_inv₀ hs0 |>.2 hs1
      linarith
    have hAbl : Ab * (1 + Real.log n) ≤ 13 * mixedConst ι c r₀ B * s ^ 4 := by
      have hm0 := mixedConst_nonneg ι hc r₀ hB
      calc Ab * (1 + Real.log n) ≤ mixedConst ι c r₀ B * s ^ 5 * (13 * s⁻¹) :=
            mul_le_mul hAbs hlog' (by linarith [Real.log_natCast_nonneg n]) (by positivity)
        _ = 13 * mixedConst ι c r₀ B * s ^ 4 := by field_simp
    have hJ1 : (s ^ 4)⁻¹ ≤ √((max (max r₀ 1) J₁ : ℕ) : ℝ) := by
      have h8 : (s ^ 8)⁻¹ ≤ ((max (max r₀ 1) J₁ : ℕ) : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
      have : (s ^ 4)⁻¹ = √((s ^ 8)⁻¹) := by
        rw [show s ^ 8 = (s ^ 4) ^ 2 by ring, Real.sqrt_inv, Real.sqrt_sq (by positivity)]
      rw [this]
      exact Real.sqrt_le_sqrt h8
    have hAas : 4 * Aa / √((max (max r₀ 1) J₁ : ℕ) : ℝ) ≤ 4 * Aa * s ^ 4 := by
      have hpos : 0 < (s ^ 4)⁻¹ := by positivity
      calc 4 * Aa / √((max (max r₀ 1) J₁ : ℕ) : ℝ) ≤ 4 * Aa / (s ^ 4)⁻¹ :=
            div_le_div_of_nonneg_left (by positivity) hpos hJ1
        _ = 4 * Aa * s ^ 4 := by rw [div_inv_eq_mul]
    have hJ0 : (0 : ℝ) ≤ ((max r₀ 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((max r₀ 1 : ℕ) : ℝ) * Ac + Ab * (1 + Real.log n) +
          4 * Aa / √((max (max r₀ 1) J₁ : ℕ) : ℝ)
        ≤ ((max r₀ 1 : ℕ) : ℝ) * (c₃ * A₃ * B ^ 3 / 6 * s ^ 4) +
          13 * mixedConst ι c r₀ B * s ^ 4 + 4 * Aa * s ^ 4 := by
          gcongr
    _ = thirdSmoothConst ι c r₀ B * s ^ 4 := by
          rw [thirdSmoothConst, ← hc₃, ← hA₃, hAa]; ring

end Main

section Convex

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → Type*} [∀ i, Fintype (X i)]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- For `1 ≤ n < N`: `1 ≤ N^{1/3} n^{-1/3}`. -/
theorem one_le_rpow_third_mul_of_lt {n N : ℕ} (hn : 0 < n) (hnN : n < N) :
    1 ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN.le
  rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, ← Real.div_rpow (by positivity) hn0.le]
  exact Real.one_le_rpow ((one_le_div hn0).2 hnN') (by norm_num)

/-- **Reservoir Lindeberg, pass 2** (infrastructure toward Theorem 7.11; not Theorem 7.11, no
statement-index entry; a Lindeberg/Bentkus-type construction, not a cited result). Independent
bounded centred summands with finite laws whose Gaussian twins satisfy `ReservoirCond` are within
`reservoirThirdConst ι c r₀ B · n^{-1/3}` of their twin Gaussian law, uniformly over all convex sets
(measurable or not), for every `n ≥ 1`. Unlike pass 1, no `r₀ ≤ n` hypothesis is needed. -/
theorem abs_pexp_convex_sub_twinLaw_le_third {p : ∀ i, X i → ℝ} {Y : ∀ i, X i → ι → ℝ}
    {L : κ → Matrix ι ι ℝ} (e : Fin n ≃ κ) (hn : 0 < n) (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) (hmean : ∀ i a, ∑ x, p i x * Y i x a = 0)
    (hcov : ∀ i a b, ∑ x, p i x * (Y i x a * Y i x b) = (L i * (L i)ᵀ) a b)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i x, ‖Y i x‖ ≤ B / √(n : ℝ))
    {c : ℝ} (hc : 0 < c) {r₀ : ℕ} (hres : ReservoirCond e L c r₀)
    {K : Set (ι → ℝ)} (hK : Convex ℝ K) :
    |Stein.pexp p (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (∑ i, Y i (ω i))) - (twinLaw L).real K| ≤
      reservoirThirdConst ι c r₀ B * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hpos : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hS0 := shellConst_nonneg ι c
  have hT0 := thirdSmoothConst_nonneg ι hc r₀ hB
  have hN0 : 0 ≤ (sharpBurnIn ι c r₀ B : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hN : sharpBurnIn ι c r₀ B ≤ n
  · have hr₀n : r₀ ≤ n := le_trans (le_max_left _ _) hN
    have hsh : (twinLaw L).real (shellSet ((n : ℝ) ^ (-(1 / 3 : ℝ))) K) ≤
        shellConst ι c * (n : ℝ) ^ (-(1 / 3 : ℝ)) :=
      (twinLaw_convexShell_le hres hr₀n hn hc hK hpos.le).trans_eq (by unfold shellConst; ring)
    have h := abs_pexp_indicator_sub_le_of_smooth_supp hp0 (fun ω ↦ ∑ i, Y i (ω i)) (twinLaw L)
      hpos K hsh (fun φ hφ h01 hd hsupp ↦ abs_pexp_sub_twinLaw_le_smooth_third e hn hp0 hp1 hmean
        hcov hB hb hc hres hN hK hφ h01 hd hsupp)
    refine h.trans ?_
    rw [reservoirThirdConst]
    nlinarith
  · push_neg at hN
    have hP0 : 0 ≤ Stein.pexp p (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (∑ i, Y i (ω i))) :=
      Stein.pexp_nonneg hp0 fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
    have hP1 : Stein.pexp p (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (∑ i, Y i (ω i))) ≤ 1 :=
      (Stein.pexp_mono hp0 (G := fun _ ↦ (1 : ℝ)) fun ω ↦ by
        by_cases h : ∑ i, Y i (ω i) ∈ K
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h]; exact zero_le_one).trans_eq (Stein.pexp_const hp1 1)
    have hm0 : 0 ≤ (twinLaw L).real K := measureReal_nonneg
    have hm1 : (twinLaw L).real K ≤ 1 := measureReal_le_one
    have h1 : |Stein.pexp p (fun ω ↦ K.indicator (fun _ ↦ (1 : ℝ)) (∑ i, Y i (ω i))) -
        (twinLaw L).real K| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have h2 := one_le_rpow_third_mul_of_lt hn hN
    refine h1.trans (h2.trans ?_)
    rw [reservoirThirdConst]
    nlinarith

end Convex

end StatisticalRL.Probability.ReservoirSharp

import Formalization.Analysis.StochasticResolventSeries

open scoped BigOperators Matrix
namespace StatisticalRL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stochasticMatrix_resolvent_nonneg (P : Matrix ι ι ℝ)
    (hp : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (i j : ι) :
    0 ≤ ((1 - γ • P)⁻¹) i j := by
  have hsum := stochasticMatrix_discounted_powers_summable P hp hs γ hγ hγ1
  have hinv : (1 - γ • P)⁻¹ = ∑' n : ℕ, (γ • P) ^ n :=
    Matrix.inv_eq_left_inv hsum.tsum_pow_mul_one_sub
  rw [hinv, tsum_apply hsum, tsum_apply (Pi.summable.mp hsum i)]
  apply tsum_nonneg
  intro n
  rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (pow_nonneg hγ _) (stochasticMatrix_pow_nonneg P hp n i j)

theorem stochasticMatrix_resolvent_rowSum (P : Matrix ι ι ℝ)
    (hp : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (i : ι) :
    ∑ j, ((1 - γ • P)⁻¹) i j = 1 / (1 - γ) := by
  have hsum := stochasticMatrix_discounted_powers_summable P hp hs γ hγ hγ1
  let A : Matrix ι ι ℝ := 1 - γ • P
  have hu : IsUnit A := ⟨⟨A, ∑' n : ℕ, (γ • P)^n,
    hsum.one_sub_mul_tsum_pow, hsum.tsum_pow_mul_one_sub⟩, rfl⟩
  letI : Invertible A := hu.invertible
  have hone : A⁻¹ *ᵥ (fun _ => 1) = fun _ => 1 / (1 - γ) := by
    apply Matrix.inv_mulVec_eq_vec
    funext s
    change (1 : ℝ) = ((1 - γ • P) *ᵥ (fun _ => 1 / (1 - γ))) s
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    rw [← Finset.sum_mul, hs]
    have hd : 1 - γ ≠ 0 := ne_of_gt (sub_pos.mpr hγ1)
    field_simp
  have hh := congrFun hone i
  simpa only [A, Matrix.mulVec, dotProduct, mul_one] using hh

theorem stochasticMatrix_resolvent_rowNorm [Nonempty ι] (P : Matrix ι ι ℝ)
    (hp : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    ‖fun i => ∑ j, |((1 - γ • P)⁻¹) i j|‖ = 1 / (1 - γ) := by
  have hrows : (fun i => ∑ j, |((1 - γ • P)⁻¹) i j|) =
      fun _ => 1 / (1 - γ) := by
    funext i
    simp_rw [abs_of_nonneg (stochasticMatrix_resolvent_nonneg P hp hs γ hγ hγ1 i _)]
    exact stochasticMatrix_resolvent_rowSum P hp hs γ hγ hγ1 i
  rw [hrows]
  simp [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hγ1.le)]

end StatisticalRL

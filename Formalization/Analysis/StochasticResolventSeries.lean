import Formalization.MDP.CoreDefinitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Row-stochastic resolvents for the book's maximum row-sum norm.
This generic prerequisite does not yet certify the two policy matrices. -/

open scoped BigOperators Matrix
namespace StatisticalRL

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stochasticMatrix_pow_nonneg (P : Matrix ι ι ℝ)
    (hp : ∀ i j, 0 ≤ P i j) (n : ℕ) (i j : ι) : 0 ≤ (P ^ n) i j := by
  induction n generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (hp k j)

theorem stochasticMatrix_pow_sum (P : Matrix ι ι ℝ)
    (hs : ∀ i, ∑ j, P i j = 1) (n : ℕ) (i : ι) :
    ∑ j, (P ^ n) i j = 1 := by
  induction n with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hs, mul_one]
    exact ih

theorem stochasticMatrix_pow_entry_le_one (P : Matrix ι ι ℝ)
    (hp : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (n : ℕ) (i j : ι) : (P ^ n) i j ≤ 1 := by
  calc
    _ ≤ ∑ k, (P ^ n) i k := Finset.single_le_sum
      (fun k _ => stochasticMatrix_pow_nonneg P hp n i k) (Finset.mem_univ j)
    _ = 1 := stochasticMatrix_pow_sum P hs n i

theorem stochasticMatrix_discounted_powers_summable (P : Matrix ι ι ℝ)
    (hp : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    Summable (fun n : ℕ => (γ • P) ^ n) := by
  apply Pi.summable.mpr
  intro i
  apply Pi.summable.mpr
  intro j
  apply Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_geometric_of_lt_one hγ hγ1)
  · rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (pow_nonneg hγ _) (stochasticMatrix_pow_nonneg P hp n i j)
  · rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
    exact mul_le_of_le_one_right (pow_nonneg hγ _)
      (stochasticMatrix_pow_entry_le_one P hp hs n i j)

theorem stochasticMatrix_resolvent_series (P : Matrix ι ι ℝ)
    (hp : ∀ i j, 0 ≤ P i j) (hs : ∀ i, ∑ j, P i j = 1)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    (1 - γ • P)⁻¹ = 1 + ∑' n : ℕ, (γ • P) ^ (n + 1) := by
  have hsum := stochasticMatrix_discounted_powers_summable P hp hs γ hγ hγ1
  have hinv : (1 - γ • P)⁻¹ = ∑' n : ℕ, (γ • P) ^ n :=
    Matrix.inv_eq_left_inv hsum.tsum_pow_mul_one_sub
  rw [hinv, hsum.tsum_eq_zero_add]
  simp

end StatisticalRL

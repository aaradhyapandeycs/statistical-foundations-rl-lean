import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Variance of mixtures (finite)

* `sum_sq_sub_mean_le`: for a probability vector `p`, `∑ p (g − ⟨p,g⟩)² ≤ ∑ p (g − c)²` for every
  `c` (the variance is the least second moment about a point).
* `mixture_variance_ge`: the weighted average of the variances of components is at most the
  variance of the mixture.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL

/-! ### Mixture variance -/

/-- The variance is the least second moment about a point. -/
theorem sum_sq_sub_mean_le {Ω : Type*} [Fintype Ω] (p g : Ω → ℝ) (hp1 : ∑ o, p o = 1) (c : ℝ) :
    ∑ o, p o * (g o - ∑ o', p o' * g o') ^ 2 ≤ ∑ o, p o * (g o - c) ^ 2 := by
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = ∑ o', p o' * g o' := ⟨_, rfl⟩
  rw [← hμ]
  have hdiff : ∑ o, p o * (g o - c) ^ 2 - ∑ o, p o * (g o - μ) ^ 2 = (μ - c) ^ 2 := by
    rw [← sum_sub_distrib]
    have : ∀ o, p o * (g o - c) ^ 2 - p o * (g o - μ) ^ 2 =
        (2 * (μ - c)) * (p o * g o) - (μ ^ 2 - c ^ 2) * p o := fun o => by ring
    simp_rw [this]
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hp1, ← hμ]
    ring
  nlinarith [sq_nonneg (μ - c)]

/-- Average of component variances `≤` variance of the mixture. -/
theorem mixture_variance_ge {ι Ω : Type*} [Fintype ι] [Fintype Ω] (w : ι → ℝ) (p : ι → Ω → ℝ)
    (g : Ω → ℝ) (hw : ∀ j, 0 ≤ w j) (hp1 : ∀ j, ∑ o, p j o = 1) :
    ∑ j, w j * ∑ o, p j o * (g o - ∑ o', p j o' * g o') ^ 2 ≤
      ∑ o, (∑ j, w j * p j o) * (g o - ∑ o', (∑ j, w j * p j o') * g o') ^ 2 := by
  set c := ∑ o', (∑ j, w j * p j o') * g o'
  calc ∑ j, w j * ∑ o, p j o * (g o - ∑ o', p j o' * g o') ^ 2
      ≤ ∑ j, w j * ∑ o, p j o * (g o - c) ^ 2 :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (sum_sq_sub_mean_le _ _ (hp1 j) c) (hw j)
    _ = ∑ o, (∑ j, w j * p j o) * (g o - c) ^ 2 := by
        simp_rw [mul_sum, sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun o _ => sum_congr rfl fun j _ => by ring

end StatisticalRL

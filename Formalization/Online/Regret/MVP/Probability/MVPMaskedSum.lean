import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Sqrt

/-! Private deterministic ingredient for MVP's uniform positive-part event.
This does not assert any concentration event or probability guarantee. -/
namespace StatisticalRL.OnlineRL

open scoped BigOperators

/-- The positive-part sum is one of the subset sums. The selecting subset
may depend on the realized values; simultaneous control of every fixed
subset is what permits this final selection. -/
theorem mvp_sum_max_eq_positive_subset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) :
    (∑ i ∈ s, max (x i) 0) = ∑ i ∈ s.filter (fun i => 0 < x i), x i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hx : 0 < x i
  · simp [hx, max_eq_left hx.le]
  · simp [hx, max_eq_right (le_of_not_gt hx)]

/-- Uniform subset bounds control a data-selected positive-part sum. -/
theorem mvp_sum_max_le_of_all_subsets {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (B : ℝ)
    (h : ∀ t : Finset ι, t ⊆ s → (∑ i ∈ t, x i) ≤ B) :
    (∑ i ∈ s, max (x i) 0) ≤ B := by
  rw [mvp_sum_max_eq_positive_subset]
  exact h _ (Finset.filter_subset _ _)

/-- Enlarge the subset's nonnegative variance budget after the uniform-mask
event has been established. No extra factor equal to the number of rows is
introduced by the positive-part selection. -/
theorem mvp_sum_max_le_sqrt_budget_of_all_subsets {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x variance : ι → ℝ) (a b : ℝ) (ha : 0 ≤ a)
    (hv : ∀ i ∈ s, 0 ≤ variance i)
    (h : ∀ t : Finset ι, t ⊆ s →
      (∑ i ∈ t, x i) ≤ Real.sqrt (a * ∑ i ∈ t, variance i) + b) :
    (∑ i ∈ s, max (x i) 0) ≤ Real.sqrt (a * ∑ i ∈ s, variance i) + b := by
  apply mvp_sum_max_le_of_all_subsets
  intro t ht
  have hvar : (∑ i ∈ t, variance i) ≤ ∑ i ∈ s, variance i :=
    Finset.sum_le_sum_of_subset_of_nonneg ht (fun i hi _ => hv i hi)
  exact (h t ht).trans (add_le_add (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvar ha)) (le_refl b))

end StatisticalRL.OnlineRL

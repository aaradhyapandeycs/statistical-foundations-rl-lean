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

end StatisticalRL.OnlineRL

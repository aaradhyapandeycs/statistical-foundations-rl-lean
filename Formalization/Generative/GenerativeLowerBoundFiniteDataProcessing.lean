import Formalization.Generative.GenerativeLowerBoundLogSum

/-! Log-sum on a decoder cell, including the empty-cell case. -/
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- Log-sum for a finite cell whose constituent masses are positive. An empty
cell is permitted; its two total masses are zero. -/
theorem finite_cell_logSum {ι : Type*} [Fintype ι] (s : Finset ι)
    (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤
      ∑ i ∈ s, a i * Real.log (a i / b i) := by
  classical
  by_cases hs : s.Nonempty
  · letI : Nonempty {i // i ∈ s} := ⟨⟨hs.choose, hs.choose_spec⟩⟩
    have h := finite_positive_logSum (fun i : {i // i ∈ s} ↦ a i)
      (fun i : {i // i ∈ s} ↦ b i) (fun i ↦ ha i i.property)
      (fun i ↦ hb i i.property)
    rw [Finset.sum_coe_sort, Finset.sum_coe_sort,
      Finset.sum_coe_sort s (fun i ↦ a i * Real.log (a i / b i))] at h
    exact h
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

end StatisticalRL.GenerativeLowerBound

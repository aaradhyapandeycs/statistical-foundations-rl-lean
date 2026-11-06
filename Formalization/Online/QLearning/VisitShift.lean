import Formalization.Online.QLearning.VisitRegroup

/-! Correct source-side positive-count shift, with the endpoint included as an
inequality, not an equality. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem qLearning_zeroBasedCost_le_positiveRange (β : ℕ → ℝ) (N : ℕ)
    (hzero : β 0 = 0) (hnonneg : 0 ≤ β N) :
    (∑ n ∈ Finset.range N, β n) ≤ ∑ n ∈ Finset.Icc 1 N, β n := by
  have heq : (∑ n ∈ Finset.Icc 1 N, β n) = ∑ n ∈ Finset.range N, β (n+1) := by
    symm
    apply Finset.sum_bij (fun n _ => n+1)
    · intro n hn; simp only [Finset.mem_range] at hn; simp only [Finset.mem_Icc]; omega
    · intro a ha b hb hab; omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      refine ⟨j-1,Finset.mem_range.mpr (by omega),?_⟩
      omega
    · intro n hn; rfl
  rw [heq]
  have hfirst := Finset.sum_range_succ' β N
  have hlast := Finset.sum_range_succ β N
  rw [hzero,add_zero] at hfirst
  linarith

/-- The regrouped pre-visit costs are bounded by the source's 1..N sum
when the zero cost is zero and the terminal cost is nonnegative. -/
theorem qLearning_visitCost_le_positiveRange {Row : Type*} [Fintype Row] [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) (β : ℕ → ℝ)
    (hzero : β 0 = 0) (hnonneg : ∀ n, 0 ≤ β n) :
    (∑ k ∈ Finset.range K, β (onlineVisitCount rowAt k (rowAt k))) ≤
      ∑ r : Row, ∑ n ∈ Finset.Icc 1 (onlineVisitCount rowAt K r), β n := by
  rw [qLearning_visitCost_regroup]
  exact Finset.sum_le_sum (fun r _ => qLearning_zeroBasedCost_le_positiveRange β _ hzero (hnonneg _))
end StatisticalRL.OnlineRL

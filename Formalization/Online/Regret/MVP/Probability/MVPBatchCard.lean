import Formalization.Online.Regret.MVP.Probability.MVPBatchIndex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exact cardinality of a completed power-of-two batch. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem mvp_batch_indicator_sum (K n : ℕ) (hn : 2*n ≤ K) (c : ℝ) :
    (∑ i : Fin K, if n ≤ i.val ∧ i.val < 2*n then c else 0) = (n : ℝ)*c := by
  classical
  let S : Finset (Fin K) := Finset.univ.filter (fun i => n ≤ i.val ∧ i.val < 2*n)
  have hs : (∑ i : Fin K, if n ≤ i.val ∧ i.val < 2*n then c else 0) = ∑ i ∈ S, c := by
    simp only [S, Finset.sum_filter]
  rw [hs]
  have hbij : (∑ _j : Fin n, c) = ∑ _i ∈ S, c := by
    apply Finset.sum_bij (fun j _ => mvpBatchIndex K n hn j)
    · intro j _
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, mvpBatchIndex]
      constructor <;> omega
    · intro j _ k _ heq
      exact mvpBatchIndex_injective K n hn heq
    · intro i hi
      have hm := (Finset.mem_filter.mp hi).2
      refine ⟨⟨i.val-n, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp only [mvpBatchIndex]
      omega
    · intro j _
      rfl
  rw [← hbij]
  simp
end StatisticalRL.OnlineRL

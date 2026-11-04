import Formalization.Online.Regret.MVP.Probability.MVPBatchCard

/-! Reindex the actual batch sum by its contiguous slice. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem mvp_batch_slice_sum (K n : ℕ) (hn : 2*n ≤ K) (f : Fin K → ℝ) :
    (∑ i : Fin K, if n ≤ i.val ∧ i.val < 2*n then f i else 0) =
      ∑ j : Fin n, f (mvpBatchIndex K n hn j) := by
  classical
  let S : Finset (Fin K) := Finset.univ.filter (fun i => n ≤ i.val ∧ i.val < 2*n)
  have hs : (∑ i : Fin K, if n ≤ i.val ∧ i.val < 2*n then f i else 0) = ∑ i ∈ S, f i := by
    simp only [S, Finset.sum_filter]
  rw [hs]
  symm
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
end StatisticalRL.OnlineRL

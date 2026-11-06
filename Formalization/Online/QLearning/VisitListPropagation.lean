import Formalization.Online.QLearning.VisitMatrixIdentity

/-! Source ordered-visit propagation bound for arbitrary realized rows. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row : Type*} [Fintype Row]
attribute [local instance] Classical.propDecidable

theorem qLearning_visitList_propagation_budget (H : ℕ) (hH : 0 < H)
    (rowAt : ℕ → Row) (K : ℕ) (gap : ℕ → ℝ)
    (hgap : ∀ e, e<K → 0 ≤ gap e) :
    (∑ k ∈ Finset.range K,
      let visits := (List.range k).filter (fun e => rowAt e = rowAt k)
      let t := visits.length
      ∑ i : Fin t, onlineQRateWeight H t (i.val+1)*gap (visits.get i)) ≤
      (1+1/(H:ℝ))*(∑ e ∈ Finset.range K, gap e) := by
  classical
  calc
    _ = ∑ k ∈ Finset.range K, ∑ e ∈ Finset.range K,
      if e<k ∧ rowAt k=rowAt e then
        onlineQRateWeight H (onlineVisitCount rowAt k (rowAt e))
          (onlineVisitCount rowAt e (rowAt e)+1) * gap e else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have heq := qLearning_visitList_to_matrix H K k (Finset.mem_range.mp hk) rowAt gap
      dsimp only at heq ⊢
      rw [heq]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs with h
      · rw [h.2]
      · rfl
    _ ≤ _ := qLearning_visitPropagation_budget H hH rowAt K gap hgap
end StatisticalRL.OnlineRL

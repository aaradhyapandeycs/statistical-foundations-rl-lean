import Formalization.Online.QLearning.LaterVisitTail

/-! Reordering of all earlier-visit contributions; deterministic arbitrary
row sequence and nonnegative values, with no independence premise. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row : Type*} [Fintype Row] [DecidableEq Row]

theorem qLearning_visitPropagation_budget (H : ℕ) (hH : 0 < H)
    (rowAt : ℕ → Row) (K : ℕ) (gap : ℕ → ℝ)
    (hgap : ∀ e, e<K → 0 ≤ gap e) :
    (∑ k ∈ Finset.range K, ∑ e ∈ Finset.range K,
      if e<k ∧ rowAt k=rowAt e then
        onlineQRateWeight H (onlineVisitCount rowAt k (rowAt e))
          (onlineVisitCount rowAt e (rowAt e)+1) * gap e else 0) ≤
      (1+1/(H:ℝ))*(∑ e ∈ Finset.range K, gap e) := by
  classical
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have heK := Finset.mem_range.mp he
  let s := (Finset.range K).filter (fun k => e<k ∧ rowAt k=rowAt e)
  have ht := qLearning_laterVisit_weights_le H hH rowAt K e
  have hm := mul_le_mul_of_nonneg_right ht (hgap e heK)
  have heq : (∑ k ∈ Finset.range K,
      if e<k ∧ rowAt k=rowAt e then
        onlineQRateWeight H (onlineVisitCount rowAt k (rowAt e))
          (onlineVisitCount rowAt e (rowAt e)+1) * gap e else 0) =
      (∑ k ∈ s, onlineQRateWeight H (onlineVisitCount rowAt k (rowAt e))
          (onlineVisitCount rowAt e (rowAt e)+1)) * gap e := by
    rw [Finset.sum_mul]
    simp only [s,Finset.sum_filter]
  rw [heq]
  exact hm
end StatisticalRL.OnlineRL

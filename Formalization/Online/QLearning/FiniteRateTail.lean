import Formalization.Online.QLearning.FirstVisitBudget

/-! Finite subsets of the source's proved learning-rate tail. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem qLearning_rate_tail_finite (H i : ℕ) (hH : 0 < H) (hi : 0 < i)
    (s : Finset ℕ) :
    (∑ j ∈ s, onlineQRateWeight H (i+j) i) ≤ 1+1/(H:ℝ) := by
  have h := onlineQRateWeight_tail_sum H i hH hi
  calc
    _ ≤ ∑' j : ℕ, onlineQRateWeight H (i+j) i :=
      Summable.sum_le_tsum s (fun j _ => onlineQRateWeight_nonneg hH _ _) h.1
    _ = _ := h.2
end StatisticalRL.OnlineRL

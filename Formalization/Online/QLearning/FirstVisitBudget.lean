import Formalization.Online.QLearning.SourceBetaBudget

/-! First-visit initialization contribution on an arbitrary realized row sequence. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row : Type*} [Fintype Row] [DecidableEq Row]

theorem qLearning_firstVisit_budget (rowAt : ℕ → Row) (K H : ℕ) (hH : 0 < H) :
    (∑ k ∈ Finset.range K,
      onlineQRateWeight H (onlineVisitCount rowAt k (rowAt k)) 0 * (H:ℝ)) ≤
      (Fintype.card Row:ℝ)*(H:ℝ) := by
  classical
  let β : ℕ → ℝ := fun n => onlineQRateWeight H n 0 * H
  have heq := qLearning_visitCost_regroup rowAt K β
  change (∑ k ∈ Finset.range K, β (onlineVisitCount rowAt k (rowAt k))) ≤ _
  rw [heq]
  calc
    _ ≤ ∑ _r : Row, (H:ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases hn : 0 < onlineVisitCount rowAt K r
      · simp [β,qLearning_rate_zero_eq hH,Finset.sum_ite_eq,hn]
      · have hz : onlineVisitCount rowAt K r = 0 := by omega
        simp [hz]
    _ = _ := by simp
end StatisticalRL.OnlineRL

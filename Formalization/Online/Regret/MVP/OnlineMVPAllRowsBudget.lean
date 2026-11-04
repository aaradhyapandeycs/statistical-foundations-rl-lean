import Formalization.Online.Regret.MVP.OnlineMVPRankBudget
import Formalization.Online.Regret.T2.OnlineT2ActualCountBudget

/-! MVP count and deterministic visit-budget results. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem onlineMVP_allRows_reciprocal_le {Row : Type*} [Fintype Row] [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) (hK : 2 ≤ K) :
    (∑ k ∈ Finset.range K, onlineMVPStoredReciprocal (onlineVisitCount rowAt k (rowAt k))) ≤
      (Fintype.card Row : ℝ) * (4 * (Real.log K / Real.log 2)) := by
  classical
  have heq : (∑ k ∈ Finset.range K, onlineMVPStoredReciprocal (onlineVisitCount rowAt k (rowAt k))) =
      ∑ r : Row, ∑ k ∈ Finset.range K,
        if rowAt k = r then onlineMVPStoredReciprocal (onlineVisitCount rowAt k r) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    simp
  rw [heq]
  calc
    _ ≤ ∑ _r : Row, (4 * (Real.log K / Real.log 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [onlineMVP_actual_row_sum_eq_visit_ranks]
      have hc : onlineVisitCount rowAt K r ≤ K := by
        letI : DecidableEq Row := Classical.decEq Row
        unfold onlineVisitCount
        simpa using Finset.card_filter_le (Finset.range K) (fun j => rowAt j = r)
      have hsub : Finset.range (onlineVisitCount rowAt K r) ⊆ Finset.range K := Finset.range_mono hc
      have hmono : (∑ n ∈ Finset.range (onlineVisitCount rowAt K r), onlineMVPStoredReciprocal n) ≤
          ∑ n ∈ Finset.range K, onlineMVPStoredReciprocal n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n hn hnot
        unfold onlineMVPStoredReciprocal
        positivity
      exact hmono.trans (onlineMVP_storedReciprocal_rank_bound K hK)
    _ = _ := by simp

end StatisticalRL.OnlineRL

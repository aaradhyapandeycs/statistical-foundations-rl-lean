import Formalization.Online.Regret.MVP.OnlineMVPStoredClosedForm
import Formalization.Online.Regret.W1.OnlineW1VisitRank

/-! MVP count and deterministic visit-budget results. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

noncomputable def onlineMVPStoredReciprocal (n : ℕ) : ℝ :=
  ((max (onlineMVPStoredCount n) 1 : ℕ) : ℝ)⁻¹

theorem onlineMVP_actual_row_sum_eq_visit_ranks {Row : Type*} [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) (r : Row) :
    (∑ k ∈ Finset.range K,
      if rowAt k = r then onlineMVPStoredReciprocal (onlineVisitCount rowAt k r) else 0) =
    ∑ n ∈ Finset.range (onlineVisitCount rowAt K r), onlineMVPStoredReciprocal n := by
  exact onlineVisitCount_sum_by_rank rowAt K r onlineMVPStoredReciprocal
end StatisticalRL.OnlineRL

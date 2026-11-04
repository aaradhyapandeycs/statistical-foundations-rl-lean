import Formalization.Online.Regret.W1.OnlineW1SmallCountRanks

/-! OnlineW1AllRowsSmallCount: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- Across all finite rows, at most three visits per row have pre-count below
three; valid for every realized adaptive row sequence. -/
theorem onlineVisitCount_allRows_lowCount_le {Row : Type*} [Fintype Row] [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) :
    (∑ j ∈ Finset.range K,
      if onlineVisitCount rowAt j (rowAt j) < 3 then (1 : ℝ) else 0) ≤
      3 * Fintype.card Row := by
  classical
  have heq : (∑ j ∈ Finset.range K,
      if onlineVisitCount rowAt j (rowAt j) < 3 then (1 : ℝ) else 0) =
      ∑ r : Row, ∑ j ∈ Finset.range K,
        if rowAt j = r ∧ onlineVisitCount rowAt j r < 3 then (1 : ℝ) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp [ite_and, Finset.sum_ite_eq']
  rw [heq]
  calc
    _ ≤ ∑ _r : Row, (3 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact onlineVisitCount_lowCount_sum_le_three rowAt K r
    _ = 3 * Fintype.card Row := by simp; ring
end StatisticalRL.OnlineRL

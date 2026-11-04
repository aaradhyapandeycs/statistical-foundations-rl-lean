import Formalization.Online.Regret.W1.OnlineW1VisitRank

/-! OnlineW1SmallCountRanks: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- For any fixed row, counts 0, 1, and 2 can each be encountered at most
once along the realized visit sequence. -/
theorem onlineVisitCount_lowCount_sum_le_three {Row : Type*} [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) (r : Row) :
    (∑ j ∈ Finset.range K,
      if rowAt j = r ∧ onlineVisitCount rowAt j r < 3 then (1 : ℝ) else 0) ≤ 3 := by
  classical
  have h := onlineVisitCount_sum_by_rank rowAt K r (fun n => if n < 3 then (1 : ℝ) else 0)
  have hcard : ((Finset.range (onlineVisitCount rowAt K r)).filter (fun n => n < 3)).card ≤ 3 := by
    calc
      _ ≤ (Finset.range 3).card := Finset.card_le_card (by
        intro n hn
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2)
      _ = 3 := Finset.card_range 3
  have hsum : (∑ n ∈ Finset.range (onlineVisitCount rowAt K r),
      if n < 3 then (1 : ℝ) else 0) ≤ 3 := by
    simpa using (show (((Finset.range (onlineVisitCount rowAt K r)).filter (fun n => n < 3)).card : ℝ) ≤ 3 by exact_mod_cast hcard)
  have heq : (∑ j ∈ Finset.range K,
      if rowAt j = r ∧ onlineVisitCount rowAt j r < 3 then (1 : ℝ) else 0) =
      ∑ n ∈ Finset.range (onlineVisitCount rowAt K r), if n < 3 then (1 : ℝ) else 0 := by
    simpa only [ite_and] using h
  exact heq ▸ hsum
end StatisticalRL.OnlineRL

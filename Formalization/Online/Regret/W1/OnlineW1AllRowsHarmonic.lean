import Formalization.Online.Regret.W1.OnlineW1VisitRank

/-! OnlineW1AllRowsHarmonic: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem onlineVisitCount_allRows_reciprocal_le {Row : Type*} [Fintype Row] [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) :
    (∑ j ∈ Finset.range K,
      (onlineVisitCount rowAt j (rowAt j) : ℝ)⁻¹) ≤
      (Fintype.card Row : ℝ) * (1 + Real.log (K + 1 : ℝ)) := by
  classical
  have heq : (∑ j ∈ Finset.range K, (onlineVisitCount rowAt j (rowAt j) : ℝ)⁻¹) =
      ∑ r : Row, ∑ j ∈ Finset.range K,
        if rowAt j = r ∧ 0 < onlineVisitCount rowAt j r
          then (onlineVisitCount rowAt j r : ℝ)⁻¹ else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hn : 0 < onlineVisitCount rowAt j (rowAt j)
    · simp [ite_and, hn]
    · have hz : onlineVisitCount rowAt j (rowAt j) = 0 := by omega
      simp [ite_and, hz]
  rw [heq]
  have hrow (r : Row) : (∑ j ∈ Finset.range K,
      if rowAt j = r ∧ 0 < onlineVisitCount rowAt j r
        then (onlineVisitCount rowAt j r : ℝ)⁻¹ else 0) ≤
      1 + Real.log (K + 1 : ℝ) := by
    have h := onlineVisitCount_reciprocal_sum_le rowAt K r
    have hcount : onlineVisitCount rowAt K r ≤ K := by
      unfold onlineVisitCount
      have hc := Finset.card_filter_le (Finset.range K) (fun j => rowAt j = r)
      simp only [Finset.card_range] at hc
      convert hc using 2 <;> ext j <;> simp
    by_cases hz : onlineVisitCount rowAt K r = 0
    · have hlog : 0 ≤ Real.log (K + 1 : ℝ) := Real.log_nonneg (by
        have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg _
        linarith)
      simp only [hz, Nat.cast_zero, Real.log_zero, add_zero] at h
      linarith
    · have hp : (0 : ℝ) < onlineVisitCount rowAt K r := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      have hle : (onlineVisitCount rowAt K r : ℝ) ≤ K + 1 := by exact_mod_cast (Nat.le_succ_of_le hcount)
      have hlog := Real.log_le_log hp hle
      linarith
  calc
    _ ≤ ∑ _r : Row, (1 + Real.log (K + 1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro r _
      exact hrow r
    _ = _ := by simp; ring
end StatisticalRL.OnlineRL

import Formalization.Online.Regret.W1.OnlineW1VisitRank

/-! Factor-two reciprocal-count budget for K ≥ 2. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem onlineT2_one_add_log_le_twice_log₂ (K : ℕ) (hK : 2 ≤ K) :
    1 + Real.log K ≤ 2 * (Real.log K / Real.log 2) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have htwole : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hKlog : Real.log 2 ≤ Real.log K :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hK)
  have hnonneg : 0 ≤ Real.log K := by linarith
  rw [← mul_div_assoc]
  apply (le_div_iff₀ htwo).2
  have hprod := mul_nonneg (sub_nonneg.mpr htwole) hnonneg
  nlinarith

/-- Positive counts on a fixed row have a deterministic envelope that holds
uniformly for any adaptive row sequence, with K≥2. -/
theorem onlineT2_row_reciprocal_le_twice_log₂ {Row : Type*} [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) (hK : 2 ≤ K) (r : Row) :
    (∑ j ∈ Finset.range K,
      if rowAt j = r ∧ 0 < onlineVisitCount rowAt j r
      then (onlineVisitCount rowAt j r : ℝ)⁻¹ else 0) ≤
        2 * (Real.log K / Real.log 2) := by
  have hb := onlineVisitCount_reciprocal_sum_le rowAt K r
  have hcount : onlineVisitCount rowAt K r ≤ K := by
    classical
    unfold onlineVisitCount
    have hc := Finset.card_filter_le (Finset.range K) (fun j => rowAt j = r)
    simp only [Finset.card_range] at hc
    convert hc using 2 <;> ext j <;> simp
  have hlog : Real.log (onlineVisitCount rowAt K r : ℝ) ≤ Real.log K := by
    by_cases hz : onlineVisitCount rowAt K r = 0
    · rw [hz, Nat.cast_zero, Real.log_zero]
      exact (Real.log_nonneg (by exact_mod_cast (show 1 ≤ K by omega)))
    · apply Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hz))
      exact_mod_cast hcount
  exact hb.trans (by linarith [onlineT2_one_add_log_le_twice_log₂ K hK])
theorem onlineT2_allRows_reciprocal_le {Row : Type*} [Fintype Row] [DecidableEq Row]
    (rowAt : ℕ → Row) (K : ℕ) (hK : 2 ≤ K) :
    (∑ j ∈ Finset.range K, (onlineVisitCount rowAt j (rowAt j) : ℝ)⁻¹) ≤
      (Fintype.card Row : ℝ) * (2 * (Real.log K / Real.log 2)) := by
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
  calc
    _ ≤ ∑ _r : Row, (2 * (Real.log K / Real.log 2)) := by
      apply Finset.sum_le_sum
      intro r _
      exact onlineT2_row_reciprocal_le_twice_log₂ rowAt K hK r
    _ = _ := by simp
end StatisticalRL.OnlineRL

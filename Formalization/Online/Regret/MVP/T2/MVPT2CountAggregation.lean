import Formalization.Online.Regret.T2.OnlineT2ChargeAggregation

/-! Deterministic aggregation through the max-one reciprocal sum.
The actual operational count budget must be proved at the consumer. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem mvpT2_charge_sum_le_maxOne {ι : Type*} (s : Finset ι)
    (count : ι → ℕ) (variance : ι → ℝ) (H L c₁ c₂ R : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hv : ∀ i, 0 ≤ variance i)
    (hR : (∑ i ∈ s, (((max (count i) 1 : ℕ) : ℝ)⁻¹)) ≤ R) :
    (∑ i ∈ s, if 0 < count i then
      c₁ * Real.sqrt (variance i * L / count i) + c₂ * H * L / count i else H) ≤
      H * R + c₁ * (Real.sqrt (L * (∑ i ∈ s, variance i)) * Real.sqrt R) +
      (c₂ * H * L) * R := by
  classical
  have hpoint (i : ι) : (if count i < 1 then (1 : ℝ) else 0) ≤
      (((max (count i) 1 : ℕ) : ℝ)⁻¹) := by
    by_cases hn : count i = 0
    · simp [hn]
    · have hp : 0 < count i := Nat.pos_of_ne_zero hn
      simp only [Nat.not_lt.mpr hp, if_false]
      positivity
  have hinv (i : ι) : ((count i : ℝ)⁻¹) ≤
      (((max (count i) 1 : ℕ) : ℝ)⁻¹) := by
    by_cases hn : count i = 0
    · simp [hn]
    · have hp : 1 ≤ count i := Nat.one_le_iff_ne_zero.mpr hn
      simp [max_eq_left hp]
  have hlo : (∑ i ∈ s, if count i < 1 then (1 : ℝ) else 0) ≤ R :=
    (Finset.sum_le_sum (fun i _ => hpoint i)).trans hR
  have hsum : (∑ i ∈ s, (count i : ℝ)⁻¹) ≤ R :=
    (Finset.sum_le_sum (fun i _ => hinv i)).trans hR
  have hroot := Real.sqrt_le_sqrt hsum
  have hb := onlineT2_charge_sum_le s count variance H L c₁ c₂ hH hL hc₁ hc₂ hv
  have hsqrt : 0 ≤ Real.sqrt (L * (∑ i ∈ s, variance i)) := Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hroot hsqrt
  have hscaled := mul_le_mul_of_nonneg_left hmul hc₁
  have hzero := mul_le_mul_of_nonneg_left hlo hH
  have hlinear := mul_le_mul_of_nonneg_left hsum (show 0 ≤ c₂ * H * L by positivity)
  linarith
end StatisticalRL.OnlineRL

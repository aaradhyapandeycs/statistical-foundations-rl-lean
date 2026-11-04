import Formalization.Online.Regret.W1.OnlineW1CauchyBudget

/-! Deterministic T₂ charge aggregation; first visits and reciprocal sums are
explicit intermediate quantities, not additional source assumptions. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem onlineT2_charge_sum_le {ι : Type*} (s : Finset ι)
    (count : ι → ℕ) (variance : ι → ℝ) (H L c₁ c₂ : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hv : ∀ i, 0 ≤ variance i) :
    (∑ i ∈ s, if 0 < count i then
      c₁ * Real.sqrt (variance i * L / count i) + c₂ * H * L / count i else H) ≤
      H * (∑ i ∈ s, if count i < 1 then (1 : ℝ) else 0) +
      c₁ * (Real.sqrt (L * (∑ i ∈ s, variance i)) * Real.sqrt (∑ i ∈ s, (count i : ℝ)⁻¹)) +
      (c₂ * H * L) * (∑ i ∈ s, (count i : ℝ)⁻¹) := by
  classical
  let inv : ι → ℝ := fun i => (count i : ℝ)⁻¹
  let low : ι → ℝ := fun i => if count i < 1 then 1 else 0
  have hinv : ∀ i, 0 ≤ inv i := fun i => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hpoint (i : ι) : (if 0 < count i then
      c₁ * Real.sqrt (variance i * L / count i) + c₂ * H * L / count i else H) =
      H * low i + c₁ * Real.sqrt (L * variance i * inv i) + (c₂ * H * L) * inv i := by
    by_cases hn : 0 < count i
    · simp only [if_pos hn, low, inv, Nat.not_lt.mpr hn, if_false]
      congr 1 <;> ring_nf
    · have hz : count i = 0 := by omega
      simp [hn, hz, low, inv]
  have hs := onlineW1_sqrt_budget s variance inv (L / 2) (by positivity) hv hinv
  have hs' : (∑ i ∈ s, Real.sqrt (L * variance i * inv i)) ≤
      Real.sqrt (L * (∑ i ∈ s, variance i)) * Real.sqrt (∑ i ∈ s, inv i) := by
    convert hs using 1 <;> ring_nf
  have hm := mul_le_mul_of_nonneg_left hs' hc₁
  calc
    _ = ∑ i ∈ s, (H * low i + c₁ * Real.sqrt (L * variance i * inv i) + (c₂ * H * L) * inv i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = H * (∑ i ∈ s, low i) + c₁ * (∑ i ∈ s, Real.sqrt (L * variance i * inv i)) +
        (c₂ * H * L) * (∑ i ∈ s, inv i) := by simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by linarith
end StatisticalRL.OnlineRL

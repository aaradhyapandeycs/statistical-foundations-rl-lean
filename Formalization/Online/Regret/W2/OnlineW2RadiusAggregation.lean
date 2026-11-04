import Formalization.Online.Regret.W1.OnlineW1CauchyBudget

/-! Algebraic cumulative W₂ radius. The low-count and inverse-count sums are
left visible here and are bounded for the actual path by the established W₁
visit-rank theorems. The count estimates are consumed in the actual-path wrapper. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- Sum high-count coordinate radii and retain the explicit low-count charge. -/
theorem onlineW2_radius_sum_le {ι : Type*} (s : Finset ι)
    (count : ι → ℕ) (variance : ι → ℝ) (S H L : ℝ)
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hv : ∀ i, 0 ≤ variance i) :
    (∑ i ∈ s, if 3 ≤ count i then
      Real.sqrt (2 * S * L * variance i / count i) + S * H * L / count i
      else H) ≤
      H * (∑ i ∈ s, if count i < 3 then (1 : ℝ) else 0) +
      Real.sqrt (2 * (S * L) * (∑ i ∈ s, variance i)) *
        Real.sqrt (∑ i ∈ s, (count i : ℝ)⁻¹) +
      (S * H * L) * (∑ i ∈ s, (count i : ℝ)⁻¹) := by
  classical
  let inv : ι → ℝ := fun i => if 3 ≤ count i then (count i : ℝ)⁻¹ else 0
  let low : ι → ℝ := fun i => if count i < 3 then 1 else 0
  have hinv : ∀ i, 0 ≤ inv i := by
    intro i
    dsimp [inv]
    split_ifs <;> positivity
  have hinvle : (∑ i ∈ s, inv i) ≤ ∑ i ∈ s, (count i : ℝ)⁻¹ := by
    apply Finset.sum_le_sum
    intro i hi
    dsimp [inv]
    split_ifs with hn
    · exact le_rfl
    · exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le (count i))
  have hpoint (i : ι) : (if 3 ≤ count i then
      Real.sqrt (2 * S * L * variance i / count i) + S * H * L / count i else H) =
      H * low i + Real.sqrt (2 * (S * L) * variance i * inv i) + (S * H * L) * inv i := by
    by_cases hn : 3 ≤ count i
    · simp only [if_pos hn, low, inv, not_lt.mpr hn, if_false]
      congr 1 <;> ring_nf
    · have hn' : count i < 3 := Nat.lt_of_not_ge hn
      simp [hn, hn', low, inv]
  have hcs := onlineW1_sqrt_budget s variance inv (S * L) (mul_nonneg hS hL) hv hinv
  have hmain := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinvle)
    (Real.sqrt_nonneg (2 * (S * L) * ∑ i ∈ s, variance i))
  have hlinear := mul_le_mul_of_nonneg_left hinvle (show 0 ≤ S * H * L by positivity)
  calc
    _ = ∑ i ∈ s, (H * low i + Real.sqrt (2 * (S * L) * variance i * inv i) +
        (S * H * L) * inv i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = H * (∑ i ∈ s, low i) +
        (∑ i ∈ s, Real.sqrt (2 * (S * L) * variance i * inv i)) +
        (S * H * L) * (∑ i ∈ s, inv i) := by simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ H * (∑ i ∈ s, low i) + Real.sqrt (2 * (S * L) * (∑ i ∈ s, variance i)) *
        Real.sqrt (∑ i ∈ s, (count i : ℝ)⁻¹) +
        (S * H * L) * (∑ i ∈ s, (count i : ℝ)⁻¹) := by linarith
    _ = _ := by rfl
end StatisticalRL.OnlineRL

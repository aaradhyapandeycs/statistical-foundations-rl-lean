import Formalization.Online.Regret.W1.OnlineW1ActualRadiusAlignment
import Formalization.Online.Regret.W1.OnlineW1CauchyBudget

/-! OnlineW1RadiusAggregation: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- No concentration assumption is hidden in this algebraic estimate. -/
theorem onlineW1_trueRadius_sum_le {ι : Type*} (s : Finset ι)
    (count : ι → ℕ) (variance : ι → ℝ) (H δ : ℝ)
    (hH : 0 ≤ H) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
    (hv : ∀ i, 0 ≤ variance i) :
    (∑ i ∈ s, if 3 ≤ count i then
      Real.sqrt (2 * Real.log (1 / (2 * δ)) * variance i / count i) +
        2 * H * Real.log (1 / (2 * δ)) / (3 * count i) else H) ≤
      H * (∑ i ∈ s, if count i < 3 then (1 : ℝ) else 0) +
      Real.sqrt (2 * Real.log (1 / (2 * δ)) * (∑ i ∈ s, variance i)) *
        Real.sqrt (∑ i ∈ s, (count i : ℝ)⁻¹) +
      (2 * H * Real.log (1 / (2 * δ)) / 3) *
        (∑ i ∈ s, (count i : ℝ)⁻¹) := by
  classical
  let L := Real.log (1 / (2 * δ))
  have hL : 0 ≤ L := by
    apply (Real.log_pos ?_).le
    apply (lt_div_iff₀ (by positivity : 0 < 2 * δ)).2
    linarith
  let inv : ι → ℝ := fun i => if 3 ≤ count i then (count i : ℝ)⁻¹ else 0
  let low : ι → ℝ := fun i => if count i < 3 then 1 else 0
  have hinv : ∀ i, 0 ≤ inv i := by
    intro i
    dsimp [inv]
    split_ifs <;> positivity
  have hlow : ∀ i, 0 ≤ low i := by
    intro i
    dsimp [low]
    split_ifs <;> norm_num
  have hinvle : (∑ i ∈ s, inv i) ≤ ∑ i ∈ s, (count i : ℝ)⁻¹ := by
    apply Finset.sum_le_sum
    intro i hi
    dsimp [inv]
    split_ifs with hn
    · exact le_rfl
    · exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le (count i))
  have hpoint (i : ι) : (if 3 ≤ count i then
      Real.sqrt (2 * L * variance i / count i) + 2 * H * L / (3 * count i) else H) =
      H * low i + Real.sqrt (2 * L * variance i * inv i) + (2 * H * L / 3) * inv i := by
    by_cases hn : 3 ≤ count i
    · simp only [if_pos hn, low, inv, not_lt.mpr hn, if_false]
      congr 1 <;> ring_nf
    · have hn' : count i < 3 := Nat.lt_of_not_ge hn
      simp [hn, hn', low, inv]
  have hcs := onlineW1_sqrt_budget s variance inv L hL hv hinv
  have hsqrt := Real.sqrt_le_sqrt hinvle
  have hmain := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg (2 * L * ∑ i ∈ s, variance i))
  have hlinear := mul_le_mul_of_nonneg_left hinvle (show 0 ≤ 2 * H * L / 3 by positivity)
  calc
    _ = ∑ i ∈ s, (H * low i + Real.sqrt (2 * L * variance i * inv i) + (2 * H * L / 3) * inv i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = H * (∑ i ∈ s, low i) +
        (∑ i ∈ s, Real.sqrt (2 * L * variance i * inv i)) +
        (2 * H * L / 3) * (∑ i ∈ s, inv i) := by simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ H * (∑ i ∈ s, low i) + Real.sqrt (2 * L * (∑ i ∈ s, variance i)) *
        Real.sqrt (∑ i ∈ s, (count i : ℝ)⁻¹) +
        (2 * H * L / 3) * (∑ i ∈ s, (count i : ℝ)⁻¹) := by linarith
    _ = _ := by rfl
end StatisticalRL.OnlineRL

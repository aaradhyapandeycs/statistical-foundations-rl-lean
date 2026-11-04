import Formalization.Online.Regret.W3.OnlineW3ActualFixedRadius
import Formalization.Online.Regret.W3.OnlineW3ActualAdaptiveRadius
import Formalization.Online.Regret.W2.OnlineW2RadiusAggregation
import Formalization.Online.Regret.W1.OnlineW1RadiusAggregation

/-! Summation of W₃ fixed and adaptive radii, keeping low counts and reciprocal
ranks explicit for the subsequent actual-history visit-count specialization. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem onlineW3_combined_radius_sum_le {ι : Type*} (s : Finset ι)
    (count : ι → ℕ) (fixed adaptive : ι → ℝ) (S H δ : ℝ)
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
    (hf : ∀ i, 0 ≤ fixed i) (ha : ∀ i, 0 ≤ adaptive i) :
    (∑ i ∈ s, ((if 3 ≤ count i then
      Real.sqrt (2 * Real.log (1 / (2 * δ)) * fixed i / count i) +
        2 * H^2 * Real.log (1 / (2 * δ)) / (3 * count i) else H^2) +
      (if 3 ≤ count i then
        Real.sqrt (2 * S * Real.log (1 / δ) * adaptive i / count i) +
          S * H^2 * Real.log (1 / δ) / count i else H^2))) ≤
    2 * H^2 * (∑ i ∈ s, if count i < 3 then (1 : ℝ) else 0) +
      Real.sqrt (2 * Real.log (1 / (2 * δ)) * (∑ i ∈ s, fixed i)) *
        Real.sqrt (∑ i ∈ s, (count i : ℝ)⁻¹) +
      Real.sqrt (2 * (S * Real.log (1 / δ)) * (∑ i ∈ s, adaptive i)) *
        Real.sqrt (∑ i ∈ s, (count i : ℝ)⁻¹) +
      (2 * H^2 * Real.log (1 / (2 * δ)) / 3 + S * H^2 * Real.log (1 / δ)) *
        (∑ i ∈ s, (count i : ℝ)⁻¹) := by
  have hL : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    apply (one_le_div hδ).2
    linarith
  have hfixed := onlineW1_trueRadius_sum_le s count fixed (H^2) δ (sq_nonneg H) hδ hδsmall hf
  have hadapt := onlineW2_radius_sum_le s count adaptive S (H^2) (Real.log (1 / δ))
    hS (sq_nonneg H) hL ha
  rw [Finset.sum_add_distrib]
  nlinarith
end StatisticalRL.OnlineRL

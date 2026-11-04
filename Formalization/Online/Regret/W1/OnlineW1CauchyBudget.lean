import Mathlib.Data.Real.Sqrt

/-! OnlineW1CauchyBudget: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- A sum of pointwise Bernstein square-root terms is controlled by the
product of the accumulated variance and reciprocal-count budgets. -/
theorem onlineW1_sqrt_budget {ι : Type*} (s : Finset ι)
    (variance inverseCount : ι → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hv : ∀ i, 0 ≤ variance i)
    (hi : ∀ i, 0 ≤ inverseCount i) :
    (∑ i ∈ s, Real.sqrt (2 * L * variance i * inverseCount i)) ≤
      Real.sqrt (2 * L * (∑ i ∈ s, variance i)) *
        Real.sqrt (∑ i ∈ s, inverseCount i) := by
  have hp : ∀ i, 0 ≤ 2 * L * variance i := by
    intro i
    exact mul_nonneg (mul_nonneg (by norm_num) hL) (hv i)
  have hs := Real.sum_sqrt_mul_sqrt_le s hp hi
  have heq : (∑ i ∈ s, Real.sqrt (2 * L * variance i * inverseCount i)) =
      ∑ i ∈ s, Real.sqrt (2 * L * variance i) * Real.sqrt (inverseCount i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Real.sqrt_mul (hp i) (inverseCount i)
  rw [heq]
  convert hs using 1
  rw [← Finset.mul_sum]
end StatisticalRL.OnlineRL

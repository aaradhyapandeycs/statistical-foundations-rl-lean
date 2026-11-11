import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Summability and half-L1 bounds for countable probability differences. -/

open scoped BigOperators
namespace StatisticalRL.QLearning.CountablePinsker

/-- Absolute differences of two nonnegative finite-mass sequences are
summable, by domination with the sum of their masses. -/
theorem qCountable_abs_sub_summable
    {Ω : Type*} [Countable Ω] (p q : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hpSum : HasSum p 1) (hqSum : HasSum q 1) :
    Summable (fun ω ↦ |p ω - q ω|) := by
  have hpoint (ω : Ω) : |p ω - q ω| ≤ p ω + q ω := by
    apply abs_le.mpr
    constructor <;> linarith [hp ω, hq ω]
  exact Summable.of_nonneg_of_le (fun ω ↦ abs_nonneg _) hpoint
    (hpSum.summable.add hqSum.summable)

end StatisticalRL.QLearning.CountablePinsker

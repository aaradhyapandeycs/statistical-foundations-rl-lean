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

/-- Countable half-L1 total variation, in the numerator/reference order. -/
noncomputable def qCountableTV_halfL1
    {Ω : Type*} [Countable Ω] (p q : Ω → ℝ) : ℝ :=
  (1 / 2) * ∑' ω, |p ω - q ω|

/-- The countable half-L1 value of probability masses lies in `[0,1]`. -/
theorem qCountableTV_halfL1_bounds
    {Ω : Type*} [Countable Ω] (p q : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hpSum : HasSum p 1) (hqSum : HasSum q 1) :
    0 ≤ qCountableTV_halfL1 p q ∧ qCountableTV_halfL1 p q ≤ 1 := by
  have hd := qCountable_abs_sub_summable p q hp hq hpSum hqSum
  have hpoint (ω : Ω) : |p ω - q ω| ≤ p ω + q ω := by
    apply abs_le.mpr
    constructor <;> linarith [hp ω, hq ω]
  have hsum : (∑' ω, |p ω - q ω|) ≤ 2 := by
    calc
      _ ≤ ∑' ω, (p ω + q ω) := hd.tsum_le_tsum hpoint
        (hpSum.summable.add hqSum.summable)
      _ = 1 + 1 := by rw [hpSum.summable.tsum_add hqSum.summable,
        hpSum.tsum_eq, hqSum.tsum_eq]
      _ = 2 := by norm_num
  constructor
  · unfold qCountableTV_halfL1
    exact mul_nonneg (by norm_num) (tsum_nonneg (fun ω ↦ abs_nonneg _))
  · unfold qCountableTV_halfL1
    nlinarith [mul_le_mul_of_nonneg_left hsum (by norm_num : 0 ≤ (1 / 2 : ℝ))]

end StatisticalRL.QLearning.CountablePinsker

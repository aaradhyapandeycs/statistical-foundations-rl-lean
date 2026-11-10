import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Centered bounded-payoff comparison with the exact half-L1 factor. -/
namespace StatisticalRL.QLearning
open scoped BigOperators

/-- Bounded payoff difference under two actual normalized nonnegative masses.
The right side is half-L1, the source's TV normalization. -/
theorem qStopped_bounded_payoff_halfL1 {ι : Type*}
    (p q R : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : HasSum p 1) (hqsum : HasSum q 1)
    (hR : ∀ i, 0 ≤ R i ∧ R i ≤ 1) :
    |(∑' i, q i * R i) - ∑' i, p i * R i| ≤
      (1 / 2 : ℝ) * ∑' i, |q i - p i| := by
  have hsp : Summable (fun i => p i * R i) :=
    Summable.of_nonneg_of_le
      (fun i => mul_nonneg (hp i) (hR i).1)
      (fun i => mul_le_of_le_one_right (hp i) (hR i).2) hpsum.summable
  have hsq : Summable (fun i => q i * R i) :=
    Summable.of_nonneg_of_le
      (fun i => mul_nonneg (hq i) (hR i).1)
      (fun i => mul_le_of_le_one_right (hq i) (hR i).2) hqsum.summable
  have hd : Summable (fun i => q i - p i) := hqsum.summable.sub hpsum.summable
  have hd0 : (∑' i, (q i - p i)) = 0 := by
    rw [hqsum.summable.tsum_sub hpsum.summable, hqsum.tsum_eq, hpsum.tsum_eq]
    ring
  have habs : Summable (fun i => |q i - p i|) := hd.abs
  have hcenter : ∀ i, |R i - (1 / 2 : ℝ)| ≤ 1 / 2 := by
    intro i
    exact abs_le.mpr ⟨by linarith [(hR i).1], by linarith [(hR i).2]⟩
  have hnorm : ∀ i, ‖(q i - p i) * (R i - (1 / 2 : ℝ))‖ ≤
      (1 / 2 : ℝ) * |q i - p i| := by
    intro i
    rw [Real.norm_eq_abs, abs_mul, mul_comm (1 / 2 : ℝ)]
    exact mul_le_mul_of_nonneg_left (hcenter i) (abs_nonneg _)
  have hnormsum : Summable (fun i => ‖(q i - p i) * (R i - (1 / 2 : ℝ))‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hnorm (habs.mul_left (1 / 2))
  have heq : (∑' i, (q i - p i) * (R i - (1 / 2 : ℝ))) =
      (∑' i, q i * R i) - ∑' i, p i * R i := by
    have hpoint : (fun i => (q i - p i) * (R i - (1 / 2 : ℝ))) =
        fun i => (q i * R i - p i * R i) - (q i - p i) * (1 / 2 : ℝ) := by
      funext i
      ring
    rw [hpoint, (hsq.sub hsp).tsum_sub (hd.mul_right (1 / 2)),
      hsq.tsum_sub hsp, tsum_mul_right, hd0]
    ring
  calc
    |(∑' i, q i * R i) - ∑' i, p i * R i| =
        ‖∑' i, (q i - p i) * (R i - (1 / 2 : ℝ))‖ := by
          rw [heq, Real.norm_eq_abs]
    _ ≤ ∑' i, ‖(q i - p i) * (R i - (1 / 2 : ℝ))‖ :=
      norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' i, (1 / 2 : ℝ) * |q i - p i| :=
      hnormsum.tsum_le_tsum hnorm (habs.mul_left (1 / 2))
    _ = (1 / 2 : ℝ) * ∑' i, |q i - p i| := tsum_mul_left

/-- Pinsker and KL enter only as explicit separate numerical inputs. The
bounded-payoff estimate itself does not assume either probability inequality. -/
theorem qStopped_bounded_payoff_of_halfL1_bound {ι : Type*}
    (p q R : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : HasSum p 1) (hqsum : HasSum q 1)
    (hR : ∀ i, 0 ≤ R i ∧ R i ≤ 1) (C : ℝ)
    (hTV : (1 / 2 : ℝ) * ∑' i, |q i - p i| ≤ C) :
    |(∑' i, q i * R i) - ∑' i, p i * R i| ≤ C :=
  (qStopped_bounded_payoff_halfL1 p q R hp hq hpsum hqsum hR).trans hTV

end StatisticalRL.QLearning

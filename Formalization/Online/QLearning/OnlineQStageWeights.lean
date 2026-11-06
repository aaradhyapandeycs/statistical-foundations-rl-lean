import Mathlib

/-!
# Geometric stage weights

`(1 + 1/H)^h ≤ exp(h/H) ≤ e` for `h ≤ H` (from `x + 1 ≤ exp x`), and hence
`∑_{h<H} ((1+1/H)^h)² v h ≤ e² ∑_{h<H} v h` for `v ≥ 0`. Deterministic only.
-/

open scoped BigOperators

namespace StatisticalRL.OnlineQStageWeightsPrivate

theorem geometricStageWeight_le_exp (H h : ℕ) (hH : 0 < H) (hh : h ≤ H) :
    (1 + 1 / (H : ℝ)) ^ h ≤ Real.exp 1 := by
  have hHr : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have h0 : 0 ≤ 1 + 1 / (H : ℝ) := by positivity
  have h1 : 1 + 1 / (H : ℝ) ≤ Real.exp (1 / H) := by
    have := Real.add_one_le_exp (1 / (H : ℝ)); linarith
  have hfrac : (h : ℝ) * (1 / H) ≤ 1 := by
    rw [mul_one_div, div_le_one hHr]; exact_mod_cast hh
  calc (1 + 1 / (H : ℝ)) ^ h ≤ (Real.exp (1 / H)) ^ h := pow_le_pow_left₀ h0 h1 h
    _ = Real.exp (h * (1 / H)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hfrac

theorem geometricStageWeightedVariance_le (H : ℕ) (hH : 0 < H) (v : ℕ → ℝ)
    (hv : ∀ h < H, 0 ≤ v h) :
    (∑ h ∈ Finset.range H, ((1 + 1 / (H : ℝ)) ^ h) ^ 2 * v h) ≤
      Real.exp 2 * ∑ h ∈ Finset.range H, v h := by
  have he : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hmem
  have hh : h < H := Finset.mem_range.mp hmem
  have hw0 : 0 ≤ (1 + 1 / (H : ℝ)) ^ h := by positivity
  have hw := geometricStageWeight_le_exp H h hH hh.le
  have hsq : ((1 + 1 / (H : ℝ)) ^ h) ^ 2 ≤ Real.exp 2 := by
    rw [he]; exact pow_le_pow_left₀ hw0 hw 2
  exact mul_le_mul_of_nonneg_right hsq (hv h hh)
end StatisticalRL.OnlineQStageWeightsPrivate

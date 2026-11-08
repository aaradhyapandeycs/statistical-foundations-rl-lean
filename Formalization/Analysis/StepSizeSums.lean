import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential

/-!
# Elementary sums for polynomially decaying step sizes

Reusable real-analysis facts for stochastic-approximation schedules `η_t = η₀ t^{-p}`:

* `sum_range_succ_rpow_neg_ge`: `t^{1-p} ≤ ∑_{i=1}^t i^{-p}` for `0 ≤ p < 1` (each term is at
  least `t^{-p}`; no integral comparison needed).
* `exp_neg_le_factorial_div_pow`: `e^{-x} ≤ n!/x^n` for `x > 0`.
* `sum_range_inv_succ_sq_le_two`: `∑_{t=1}^T t^{-2} ≤ 2`.
* `sum_range_exp_neg_mul_cbrt_le`: `∑_{t=1}^T exp(-c t^{1/3}) ≤ 1440 / c^6` for `c > 0`, uniformly
  in `T` (stretched-exponential summability, via `e^{-x} ≤ 720/x^6`).
-/

open Finset Real

namespace StatisticalRL.Probability

/-- `t^{1-p} ≤ ∑_{i=1}^t i^{-p}` for `0 ≤ p < 1`. -/
theorem sum_range_succ_rpow_neg_ge (t : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (t : ℝ) ^ (1 - p) ≤ ∑ i ∈ range t, ((i + 1 : ℕ) : ℝ) ^ (-p) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [Real.zero_rpow (by linarith : (1 - p) ≠ 0)]
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hterm : ∀ i ∈ range t, (t : ℝ) ^ (-p) ≤ ((i + 1 : ℕ) : ℝ) ^ (-p) := by
    intro i hi
    have hi' : ((i + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast (mem_range.1 hi)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hi' (by linarith)
  calc (t : ℝ) ^ (1 - p) = ∑ _i ∈ range t, (t : ℝ) ^ (-p) := by
        rw [sum_const, card_range, nsmul_eq_mul, sub_eq_add_neg, Real.rpow_add htR,
          Real.rpow_one]
    _ ≤ _ := sum_le_sum hterm

/-- `e^{-x} ≤ n!/x^n` for `x > 0`. -/
theorem exp_neg_le_factorial_div_pow {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-x) ≤ n.factorial / x ^ n := by
  have h := Real.pow_div_factorial_le_exp x hx.le n
  have hxn : 0 < x ^ n := pow_pos hx n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [Real.exp_neg, le_div_iff₀ hxn, inv_mul_le_iff₀ (Real.exp_pos x)]
  rw [div_le_iff₀ hf] at h
  linarith

/-- `∑_{t=1}^T t^{-2} ≤ 2 - 2/(T+1) ≤ 2`. -/
theorem sum_range_inv_succ_sq_le (T : ℕ) :
    ∑ t ∈ range T, (((t : ℝ) + 1) ^ 2)⁻¹ ≤ 2 - 2 / ((T : ℝ) + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ]
    have hT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    have key : (((T : ℝ) + 1) ^ 2)⁻¹ ≤ 2 / ((T : ℝ) + 1) - 2 / (((T + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ hT.ne' (by positivity), inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem sum_range_inv_succ_sq_le_two (T : ℕ) :
    ∑ t ∈ range T, (((t : ℝ) + 1) ^ 2)⁻¹ ≤ 2 :=
  (sum_range_inv_succ_sq_le T).trans (by
    have : (0 : ℝ) ≤ 2 / ((T : ℝ) + 1) := by positivity
    linarith)

/-- Stretched-exponential summability, uniform in the horizon:
`∑_{t=1}^T exp(-c t^{1/3}) ≤ 1440 / c^6` for `c > 0`. -/
theorem sum_range_exp_neg_mul_cbrt_le {c : ℝ} (hc : 0 < c) (T : ℕ) :
    ∑ t ∈ range T, Real.exp (-(c * ((t : ℝ) + 1) ^ (1 / 3 : ℝ))) ≤ 1440 / c ^ 6 := by
  have hterm : ∀ t ∈ range T, Real.exp (-(c * ((t : ℝ) + 1) ^ (1 / 3 : ℝ))) ≤
      720 / c ^ 6 * (((t : ℝ) + 1) ^ 2)⁻¹ := by
    intro t _
    have ht : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have hx : 0 < c * ((t : ℝ) + 1) ^ (1 / 3 : ℝ) := mul_pos hc (Real.rpow_pos_of_pos ht _)
    refine (exp_neg_le_factorial_div_pow hx 6).trans (le_of_eq ?_)
    have h6 : (((t : ℝ) + 1) ^ (1 / 3 : ℝ)) ^ 6 = ((t : ℝ) + 1) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      norm_num
    rw [mul_pow, h6]
    norm_num [Nat.factorial]
    field_simp
  calc _ ≤ ∑ t ∈ range T, 720 / c ^ 6 * (((t : ℝ) + 1) ^ 2)⁻¹ := sum_le_sum hterm
    _ = 720 / c ^ 6 * ∑ t ∈ range T, (((t : ℝ) + 1) ^ 2)⁻¹ := by rw [mul_sum]
    _ ≤ 720 / c ^ 6 * 2 :=
        mul_le_mul_of_nonneg_left (sum_range_inv_succ_sq_le_two T) (by positivity)
    _ = 1440 / c ^ 6 := by ring

end StatisticalRL.Probability

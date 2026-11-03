import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! Scalar Bernstein envelope with the exact factorial/geometric coefficient.
No probabilistic estimate is assumed. -/
open scoped BigOperators
namespace StatisticalRL

/-- The factorial tail grows at least geometrically with ratio three. -/
theorem bernstein_factorial_lower (k : ℕ) :
    (2 : ℝ) * 3 ^ k ≤ ((k + 2).factorial : ℝ) := by
  have h := Nat.factorial_mul_pow_le_factorial (m := 2) (n := k)
  norm_num only [Nat.factorial_succ, Nat.factorial_zero] at h
  exact_mod_cast (by simpa only [Nat.add_comm] using h)

/-- Exact Bernstein scalar exponential envelope on the full |z|<3 domain. -/
theorem exp_le_one_add_add_bernstein (z : ℝ) (hz : |z| < 3) :
    Real.exp z ≤ 1 + z + z ^ 2 / (2 * (1 - |z| / 3)) := by
  have hexp : HasSum (fun k : ℕ ↦ z ^ k / (k.factorial : ℝ)) (Real.exp z) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ z
  have htail := (hasSum_nat_add_iff' 2).2 hexp
  have htail' : HasSum (fun k : ℕ ↦ z ^ (k + 2) / ((k + 2).factorial : ℝ))
      (Real.exp z - (1 + z)) := by
    simpa [Finset.sum_range_succ] using htail
  have hratio : ‖|z| / 3‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg z) (by norm_num))]
    linarith
  have hgeom := (hasSum_geometric_of_norm_lt_one hratio).mul_left (z ^ 2 / 2)
  have hterm (k : ℕ) : z ^ (k + 2) / ((k + 2).factorial : ℝ) ≤
      (z ^ 2 / 2) * (|z| / 3) ^ k := by
    have hfac := bernstein_factorial_lower k
    have hfpos : 0 < ((k + 2).factorial : ℝ) := by positivity
    calc
      _ ≤ |z| ^ (k + 2) / ((k + 2).factorial : ℝ) := by
        apply div_le_div_of_nonneg_right _ hfpos.le
        simpa only [abs_pow] using le_abs_self (z ^ (k + 2))
      _ ≤ |z| ^ (k + 2) / (2 * 3 ^ k) :=
        div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg z) _) (by positivity) hfac
      _ = (z ^ 2 / 2) * (|z| / 3) ^ k := by
        rw [pow_add, div_pow, sq_abs]
        field_simp
  have hsum := hasSum_le hterm htail' hgeom
  have hid : z ^ 2 / 2 * (1 - |z| / 3)⁻¹ = z ^ 2 / (2 * (1 - |z| / 3)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hid] at hsum
  linarith

/-- A common deterministic increment envelope may replace the realized
absolute value in the Bernstein denominator. -/
theorem exp_le_one_add_add_bernstein_of_abs_le (z r : ℝ)
    (hz : |z| ≤ r) (hr : r < 3) :
    Real.exp z ≤ 1 + z + z ^ 2 / (2 * (1 - r / 3)) := by
  have hactual := exp_le_one_add_add_bernstein z (hz.trans_lt hr)
  have hd : 0 < 2 * (1 - r / 3) := by linarith
  have hden : 2 * (1 - r / 3) ≤ 2 * (1 - |z| / 3) := by linarith
  have hc := div_le_div_of_nonneg_left (sq_nonneg z) hd hden
  linarith

end StatisticalRL

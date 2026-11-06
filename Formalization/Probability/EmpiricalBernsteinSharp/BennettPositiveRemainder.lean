import Formalization.Probability.SharpEmpiricalBernstein

/-! Private uncompiled positive-side component of the exact Bennett MGF.
The negative centered-value case and probability bounds are not asserted. -/
namespace StatisticalRL.SharpBernstein

/-- For nonnegative x≤1, the full exponential remainder at a·x is at most
x² times the full exponential remainder at a. -/
theorem exp_remainder_scaled_nonnegative (a x : ℝ)
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (a*x) ≤ 1 + a*x + x^2 * (Real.exp a - 1 - a) := by
  have haSeries : Summable (fun n : ℕ ↦ a^n / (n.factorial : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp ℝ a).summable
  have haxSeries : Summable (fun n : ℕ ↦ (a*x)^n / (n.factorial : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp ℝ (a*x)).summable
  have haTail : Summable (fun n : ℕ ↦ a^(n+2) / ((n+2).factorial : ℝ)) :=
    (summable_nat_add_iff (f := fun n : ℕ ↦ a^n / (n.factorial : ℝ)) 2).2 haSeries
  have haxTail : Summable (fun n : ℕ ↦ (a*x)^(n+2) / ((n+2).factorial : ℝ)) :=
    (summable_nat_add_iff (f := fun n : ℕ ↦ (a*x)^n / (n.factorial : ℝ)) 2).2 haxSeries
  have hbound (n : ℕ) : (a*x)^(n+2) / ((n+2).factorial : ℝ) ≤
      x^2 * (a^(n+2) / ((n+2).factorial : ℝ)) := by
    have hp : x^n ≤ 1 := pow_le_one₀ hx hx1
    calc
      _ = (a^(n+2) / ((n+2).factorial : ℝ)) * x^2 * x^n := by
        simp only [mul_pow, pow_add]
        ring
      _ ≤ (a^(n+2) / ((n+2).factorial : ℝ)) * x^2 * 1 := by
        exact mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hsum := Summable.tsum_le_tsum hbound haxTail (haTail.mul_left (x^2))
  rw [tsum_mul_left] at hsum
  have haExp : (∑' n : ℕ, a^n / (n.factorial : ℝ)) = Real.exp a := by
    simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp ℝ a).tsum_eq
  have haxExp : (∑' n : ℕ, (a*x)^n / (n.factorial : ℝ)) = Real.exp (a*x) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ℝ (a*x)).tsum_eq
  have haSplit := haSeries.sum_add_tsum_nat_add 2
  have haxSplit := haxSeries.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, pow_zero, pow_one, div_one, zero_add] at haSplit haxSplit
  rw [haExp] at haSplit
  rw [haxExp] at haxSplit
  nlinarith [hsum]
end StatisticalRL.SharpBernstein

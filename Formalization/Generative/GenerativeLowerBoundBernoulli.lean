import Formalization.Generative.PolicyEvaluationSampleAssembly

/-! Scalar Bernoulli KL bound used by the generative lower-bound argument. -/
namespace StatisticalRL.GenerativeLowerBound

/-- The explicit real expression for KL(Bern(q) || Bern(p)), for interior
parameters. Identification with measure-theoretic KL is a separate theorem. -/
noncomputable def bernoulliKLExpression (q p : ℝ) : ℝ :=
  q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p))

/-- Quadratic upper bound for the scalar Bernoulli KL expression. -/
theorem bernoulliKLExpression_le_quadratic (q p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    bernoulliKLExpression q p ≤ (q - p) ^ 2 / (p * (1 - p)) := by
  have h₁ := Real.log_le_sub_one_of_pos (div_pos hq hp)
  have h₂ := Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr hq1) (sub_pos.mpr hp1))
  have hw₁ := mul_le_mul_of_nonneg_left h₁ hq.le
  have hw₂ := mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr hq1.le)
  unfold bernoulliKLExpression
  calc
    _ ≤ q * (q / p - 1) + (1 - q) * ((1 - q) / (1 - p) - 1) := add_le_add hw₁ hw₂
    _ = (q - p) ^ 2 / (p * (1 - p)) := by
      field_simp [ne_of_gt hp, ne_of_gt (sub_pos.mpr hp1)]
      ring

/-- The exact source specialization for p≥1/2. -/
theorem bernoulliKLExpression_increment_le (p α : ℝ)
    (hp : (1 : ℝ) / 2 ≤ p) (hα : 0 < α) (hpa : p + α < 1) :
    bernoulliKLExpression (p + α) p ≤ 2 * α ^ 2 / (1 - p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  have hq : 0 < p + α := by linarith
  have h := bernoulliKLExpression_le_quadratic (p + α) p hp0 hp1 hq hpa
  have hd : 0 < 1 - p := sub_pos.mpr hp1
  have hbound : α ^ 2 / (p * (1 - p)) ≤ 2 * α ^ 2 / (1 - p) := by
    apply (div_le_div_iff₀ (by positivity : 0 < p * (1 - p)) hd).2
    have hm := mul_nonneg (show 0 ≤ 2 * p - 1 by linarith)
      (mul_nonneg (sq_nonneg α) hd.le)
    nlinarith
  have heq : p + α - p = α := by ring
  rw [heq] at h
  exact h.trans hbound

end StatisticalRL.GenerativeLowerBound

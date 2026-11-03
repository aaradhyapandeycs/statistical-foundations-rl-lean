import Formalization.Generative.PolicyEvaluationSampleAssembly

/-! Finite weighted logarithmic inequality for an information-theoretic bound. -/
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- Logarithm of a positive finite weighted average dominates the weighted
average of logarithms. All weights and values are strictly positive. -/
theorem finite_weighted_log_le_log_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i)
    (hsum : ∑ i, w i = 1) :
    (∑ i, w i * Real.log (x i)) ≤ Real.log (∑ i, w i * x i) := by
  let m := ∑ i, w i * x i
  have hm : 0 < m := Finset.sum_pos (fun i _ ↦ mul_pos (hw i) (hx i))
    Finset.univ_nonempty
  have hp (i : ι) : w i * (Real.log (x i) - Real.log m) ≤
      w i * (x i / m - 1) := by
    have ht := Real.log_le_sub_one_of_pos (div_pos (hx i) hm)
    rw [Real.log_div (ne_of_gt (hx i)) (ne_of_gt hm)] at ht
    exact mul_le_mul_of_nonneg_left ht (hw i).le
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hp i)
  have hr : (∑ i, w i * (x i / m - 1)) = 0 := by
    simp_rw [mul_sub, ← mul_div_assoc]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [mul_one, hsum]
    change m / m - 1 = 0
    rw [div_self (ne_of_gt hm)]
    ring
  have hl : (∑ i, w i * (Real.log (x i) - Real.log m)) =
      (∑ i, w i * Real.log (x i)) - Real.log m := by
    simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
  rw [hl, hr] at hh
  linarith

/-- The Hellinger affinity of positive finite probability masses. -/
noncomputable def finiteAffinity {ι : Type*} [Fintype ι] (u v : ι → ℝ) : ℝ :=
  ∑ i, Real.sqrt (u i) * Real.sqrt (v i)

/-- The oriented finite KL formula, with u the first law. -/
noncomputable def finiteKLExpression {ι : Type*} [Fintype ι] (u v : ι → ℝ) : ℝ :=
  ∑ i, u i * Real.log (u i / v i)

/-- Jensen gives log affinity at least minus half the oriented KL. -/
theorem finite_log_affinity_lower {ι : Type*} [Fintype ι] [Nonempty ι]
    (u v : ι → ℝ) (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hsum : ∑ i, u i = 1) :
    -finiteKLExpression u v / 2 ≤ Real.log (finiteAffinity u v) := by
  let x : ι → ℝ := fun i ↦ Real.sqrt (v i / u i)
  have hx (i : ι) : 0 < x i := Real.sqrt_pos.2 (div_pos (hv i) (hu i))
  have hm (i : ι) : u i * x i = Real.sqrt (u i) * Real.sqrt (v i) := by
    dsimp [x]
    rw [Real.sqrt_div (hv i).le]
    have hp : 0 < Real.sqrt (u i) := Real.sqrt_pos.2 (hu i)
    have hs := Real.sq_sqrt (hu i).le
    field_simp
    conv_lhs => rw [← hs]
    ring
  have hl (i : ι) : u i * Real.log (x i) =
      -(u i * Real.log (u i / v i)) / 2 := by
    dsimp [x]
    rw [Real.log_sqrt (div_nonneg (hv i).le (hu i).le),
      Real.log_div (ne_of_gt (hv i)) (ne_of_gt (hu i)),
      Real.log_div (ne_of_gt (hu i)) (ne_of_gt (hv i))]
    ring
  have h := finite_weighted_log_le_log_sum u x hu hx hsum
  simp_rw [hm, hl] at h
  unfold finiteAffinity finiteKLExpression
  rw [← Finset.sum_div, Finset.sum_neg_distrib] at h
  exact h

end StatisticalRL.GenerativeLowerBound

import Formalization.Generative.PolicyEvaluationSampleAssembly

/-! Finite affinity–overlap inequality via Cauchy–Schwarz. -/
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- Squared Hellinger affinity is at most twice the overlap for two finite
probability vectors. Zero coordinates are permitted in this inequality. -/
theorem finite_affinity_sq_le_two_overlap {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hsumu : ∑ i, u i = 1) (hsumv : ∑ i, v i = 1) :
    (∑ i, Real.sqrt (u i) * Real.sqrt (v i)) ^ 2 ≤
      2 * ∑ i, min (u i) (v i) := by
  let a : ι → ℝ := fun i ↦ Real.sqrt (min (u i) (v i))
  let b : ι → ℝ := fun i ↦ Real.sqrt (max (u i) (v i))
  have hab (i : ι) : a i * b i = Real.sqrt (u i) * Real.sqrt (v i) := by
    dsimp [a, b]
    rcases le_total (u i) (v i) with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h, mul_comm]
  have ha (i : ι) : a i ^ 2 = min (u i) (v i) := Real.sq_sqrt (le_min (hu i) (hv i))
  have hb (i : ι) : b i ^ 2 = max (u i) (v i) := Real.sq_sqrt (le_max_of_le_left (hu i))
  have hm : (∑ i, max (u i) (v i)) ≤ 2 := by
    calc
      _ ≤ ∑ i, (u i + v i) := Finset.sum_le_sum (fun i _ ↦ max_le (by linarith [hv i]) (by linarith [hu i]))
      _ = 2 := by rw [Finset.sum_add_distrib, hsumu, hsumv]; norm_num
  have ho : 0 ≤ ∑ i, min (u i) (v i) :=
    Finset.sum_nonneg (fun i _ ↦ le_min (hu i) (hv i))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  simp_rw [hab, ha, hb] at hc
  have ht := mul_le_mul_of_nonneg_left hm ho
  nlinarith

end StatisticalRL.GenerativeLowerBound

import Formalization.Generative.GenerativeLowerBoundLogSum

/-! Binary entropy constant for finite testing reductions. -/
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- Binary entropy is at most log 2, including zero-mass outcomes. -/
theorem binary_entropy_le_log_two (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    -(t * Real.log t) - ((1 - t) * Real.log (1 - t)) ≤ Real.log 2 := by
  by_cases h0 : t = 0
  · subst t
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    simpa using this
  by_cases h1 : t = 1
  · subst t
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    simpa using this
  have ht0 : 0 < t := lt_of_le_of_ne ht (Ne.symm h0)
  have htone : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 h1)
  let a : Bool → ℝ := fun b ↦ if b then t else 1 - t
  let b : Bool → ℝ := fun _ ↦ 1 / 2
  have ha : ∀ i, 0 < a i := by intro i; cases i <;> simp [a, ht0, htone]
  have hb : ∀ i, 0 < b i := by intro i; norm_num [b]
  have h := finite_positive_logSum a b ha hb
  have hp : Real.log (t / (1 / 2)) = Real.log t + Real.log 2 := by
    rw [Real.log_div (ne_of_gt ht0) (by norm_num)]
    have hl : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      ring
    rw [hl]
    ring
  have hq : Real.log ((1 - t) / (1 / 2)) = Real.log (1 - t) + Real.log 2 := by
    rw [Real.log_div (ne_of_gt htone) (by norm_num)]
    have hl : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      ring
    rw [hl]
    ring
  norm_num [div_eq_mul_inv] at hp hq
  simp [a, b] at h
  rw [hp, hq] at h
  nlinarith

end StatisticalRL.GenerativeLowerBound

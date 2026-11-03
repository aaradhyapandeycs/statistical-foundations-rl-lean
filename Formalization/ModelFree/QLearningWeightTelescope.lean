import Formalization.ModelFree.QLearningOptimalLateBudget

/-! positive-index source weight telescope. -/
open scoped BigOperators
namespace StatisticalRL.QLearning

/-- Exact positive-index source weight sum, including the empty interval. -/
theorem qPositiveWeight_sum_telescope (η : ℕ → ℝ) (L u : ℕ) :
    (∑ i ∈ Finset.Icc L u, qPositiveWeight η u i) =
      1 - ∏ j ∈ Finset.Icc L u, (1 - η j) := by
  induction u with
  | zero =>
    by_cases h : L = 0
    · subst L
      simp [qPositiveWeight]
    · have hL : 1 ≤ L := by omega
      simp [Finset.Icc_eq_empty_of_lt (by omega : 0 < L)]
  | succ u ih =>
    by_cases hL : L ≤ u+1
    · rw [Finset.sum_Icc_succ_top hL, Finset.prod_Icc_succ_top hL]
      have hweight : ∀ i ∈ Finset.Icc L u,
          qPositiveWeight η (u+1) i = qPositiveWeight η u i * (1 - η (u+1)) := by
        intro i hi
        have hi' := (Finset.mem_Icc.mp hi).2
        unfold qPositiveWeight
        rw [Finset.prod_Icc_succ_top (by omega)]
        ring
      rw [Finset.sum_congr rfl hweight, ← Finset.sum_mul, ih]
      simp [qPositiveWeight]
      ring
    · have hL' : u+1 < L := by omega
      simp [Finset.Icc_eq_empty_of_lt hL']

/-- Source positive late weights sum to at most one under rate-prefix bounds. -/
theorem qPositiveWeight_late_sum_le_one (η : ℕ → ℝ) (T u : ℕ)
    (hη : ∀ k, 1 ≤ k → k ≤ u → 0 ≤ η k ∧ η k ≤ 1) :
    (∑ i ∈ Finset.Icc (T/2+1) u, qPositiveWeight η u i) ≤ 1 := by
  rw [qPositiveWeight_sum_telescope]
  have hp : 0 ≤ ∏ j ∈ Finset.Icc (T/2+1) u, (1 - η j) := by
    apply Finset.prod_nonneg
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact sub_nonneg.mpr (hη j (by omega) hj'.2).2
  linarith

/-- Late squared-source-weight budget, using only source rate bounds and the
late-rate cap; it does not assume a sum-of-weights conclusion. -/
theorem qLate_weight_squares_le (η : ℕ → ℝ) (T u : ℕ) (cap : ℝ)
    (hcap : 0 ≤ cap) (hη : ∀ k, 1 ≤ k → k ≤ u → 0 ≤ η k ∧ η k ≤ 1)
    (hlate : ∀ k, T/2 < k → k ≤ u → η k ≤ cap) :
    (∑ i ∈ Finset.Icc (T/2+1) u, (qPositiveWeight η u i)^2) ≤ cap :=
  qLate_weight_squares_of_sum_le_one η T u cap hcap hη hlate
    (qPositiveWeight_late_sum_le_one η T u hη)

end StatisticalRL.QLearning

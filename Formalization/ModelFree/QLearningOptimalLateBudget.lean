import Formalization.ModelFree.QLearningOptimalFluctuationWindow

/-! finite squared-weight reduction for Q-learning. -/
open scoped BigOperators
namespace StatisticalRL.QLearning

/-- Elementary finite reduction after the separately proved source telescoping
identity. The budget and rate bounds are genuine intermediate inputs, not the
concentration or convergence conclusion. -/
theorem qLate_weight_squares_of_sum_le_one (η : ℕ → ℝ) (T u : ℕ) (cap : ℝ)
    (hcap : 0 ≤ cap)
    (hη : ∀ k, 1 ≤ k → k ≤ u → 0 ≤ η k ∧ η k ≤ 1)
    (hlate : ∀ k, T/2 < k → k ≤ u → η k ≤ cap)
    (hsum : (∑ i ∈ Finset.Icc (T/2+1) u, qPositiveWeight η u i) ≤ 1) :
    (∑ i ∈ Finset.Icc (T/2+1) u, (qPositiveWeight η u i)^2) ≤ cap := by
  calc
    _ ≤ ∑ i ∈ Finset.Icc (T/2+1) u, cap * qPositiveWeight η u i := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hwi := qPositiveWeight_late_le η T u i (by omega) hi'.2 hη cap hlate
      nlinarith [mul_nonneg hwi.1 (sub_nonneg.mpr hwi.2)]
    _ = cap * ∑ i ∈ Finset.Icc (T/2+1) u, qPositiveWeight η u i := by rw [Finset.mul_sum]
    _ ≤ cap * 1 := mul_le_mul_of_nonneg_left hsum hcap
    _ = cap := mul_one _

/- The source weight telescope and source-index reindexing are proved in subsequent modules. -/
end StatisticalRL.QLearning

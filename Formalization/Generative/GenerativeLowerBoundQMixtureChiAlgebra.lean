import Formalization.Generative.GenerativeLowerBoundQMixtureDensity

/-! Exact finite diagonal/off-diagonal bookkeeping for the Q mixture. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace StatisticalRL.GenerativeLowerBound

/-- Summing a constant diagonal d and unit off-diagonal entries counts the
exact K diagonal and K(K−1) ordered off-diagonal pairs. -/
theorem finite_diagonal_cross_sum {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] (d : ℝ) :
    (∑ i : ι, ∑ j : ι, if i = j then d else 1) =
      Fintype.card ι * d + Fintype.card ι * (Fintype.card ι - 1) := by
  classical
  have h (i : ι) : (∑ j : ι, if i = j then d else 1) =
      d + (Fintype.card ι - 1) := by
    have heq (j : ι) : (if i = j then d else 1) = 1 + (if i = j then d - 1 else 0) := by
      by_cases hij : i = j <;> simp [hij]
    simp_rw [heq]
    simp [Finset.sum_add_distrib, eq_comm]
    ring
  simp_rw [h]
  simp [Finset.sum_const, nsmul_eq_mul]

end StatisticalRL.GenerativeLowerBound

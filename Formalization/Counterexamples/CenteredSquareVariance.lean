import Formalization.Probability.Variance
import Mathlib.Tactic.NormNum

/-! A two-point counterexample to the signed centered-square coefficient-one bound. -/
namespace StatisticalRL.SourceCounterexamples
open scoped BigOperators

noncomputable def squareVarianceLaw : FiniteDistribution Bool where
  prob b := if b then (1 / 8 : ℝ) else 7 / 8
  prob_nonneg b := by cases b <;> norm_num
  sum_prob := by norm_num [Fintype.sum_bool]

def signedValue (b : Bool) : ℝ := if b then 1 else -1

theorem signedValue_abs (b : Bool) : |signedValue b| = 1 := by
  cases b <;> norm_num [signedValue]

theorem squareVarianceLaw_mean : squareVarianceLaw.expectation signedValue = -(3 / 4 : ℝ) := by
  norm_num [squareVarianceLaw, signedValue, FiniteDistribution.expectation, Fintype.sum_bool]

theorem squareVarianceLaw_variance : squareVarianceLaw.variance signedValue = (7 / 16 : ℝ) := by
  norm_num [squareVarianceLaw, signedValue, FiniteDistribution.variance,
    FiniteDistribution.expectation, Fintype.sum_bool]

theorem squareVarianceLaw_centeredSquare_variance :
    squareVarianceLaw.variance
      (fun b => (signedValue b - squareVarianceLaw.expectation signedValue)^2) = (63 / 64 : ℝ) := by
  norm_num [squareVarianceLaw_mean, squareVarianceLaw, signedValue, FiniteDistribution.variance,
    FiniteDistribution.expectation, Fintype.sum_bool]

/-- The printed coefficient one fails even on a two-point probability space
whose largest possible absolute value is exactly one. -/
theorem centeredSquare_source_coefficient_one_false :
    ¬ squareVarianceLaw.variance
      (fun b => (signedValue b - squareVarianceLaw.expectation signedValue)^2) ≤
        (1 : ℝ)^2 * squareVarianceLaw.variance signedValue := by
  rw [squareVarianceLaw_centeredSquare_variance, squareVarianceLaw_variance]
  norm_num

end StatisticalRL.SourceCounterexamples

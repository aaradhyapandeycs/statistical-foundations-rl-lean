import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-! Finite probability distributions: the real probability simplex on a finite carrier. -/
open scoped BigOperators
namespace StatisticalRL

/-- The real probability simplex on a finite carrier. -/
structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  prob_nonneg : ∀ x, 0 ≤ prob x
  sum_prob : ∑ x, prob x = 1

namespace FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

/-- Expectation under an actual finite probability vector. -/
def expectation (d : FiniteDistribution Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, d.prob x * f x

end FiniteDistribution

end StatisticalRL

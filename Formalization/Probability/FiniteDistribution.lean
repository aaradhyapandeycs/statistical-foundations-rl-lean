import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

/-- Two finite distributions with the same masses are equal. -/
@[ext]
theorem ext {d d' : FiniteDistribution Ω} (h : d.prob = d'.prob) : d = d' := by
  cases d
  cases d'
  cases h
  rfl

/-- Every mass of a finite distribution is at most one. -/
theorem prob_le_one (d : FiniteDistribution Ω) (x : Ω) : d.prob x ≤ 1 := by
  rw [← d.sum_prob]
  exact Finset.single_le_sum (fun y _ ↦ d.prob_nonneg y) (Finset.mem_univ x)

/-- The carrier of a finite distribution is nonempty. -/
theorem nonempty (d : FiniteDistribution Ω) : Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := d.sum_prob
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact zero_ne_one this

/-- On a subsingleton carrier there is only one finite distribution. -/
theorem eq_of_subsingleton [Subsingleton Ω] (d e : FiniteDistribution Ω) : d = e := by
  have hprob : ∀ (d : FiniteDistribution Ω) (a : Ω), d.prob a = 1 := by
    intro d a
    have h := d.sum_prob
    rwa [Fintype.sum_subsingleton _ a] at h
  exact ext (funext fun a ↦ by rw [hprob d a, hprob e a])

@[simp]
theorem expectation_const (d : FiniteDistribution Ω) (c : ℝ) :
    d.expectation (fun _ ↦ c) = c := by
  rw [expectation, ← Finset.sum_mul, d.sum_prob, one_mul]

end FiniteDistribution

end StatisticalRL

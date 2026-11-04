import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Basic finite distributions, discounted MDPs, and policies. -/
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

/-- The source's stationary discounted model, with its exact reward and discount bounds. -/
structure DiscountedMDP (State Action : Type*) [Fintype State] [Fintype Action] where
  state_nonempty : Nonempty State
  action_nonempty : Nonempty Action
  transition : State → Action → FiniteDistribution State
  reward : State → Action → ℝ
  reward_nonneg : ∀ s a, 0 ≤ reward s a
  reward_le_one : ∀ s a, reward s a ≤ 1
  discount : ℝ
  discount_nonneg : 0 ≤ discount
  discount_lt_one : discount < 1

/-- A stationary randomized policy assigns a probability vector over actions to each state. -/
abbrev StationaryPolicy (State Action : Type*) [Fintype Action] :=
  State → FiniteDistribution Action

end StatisticalRL

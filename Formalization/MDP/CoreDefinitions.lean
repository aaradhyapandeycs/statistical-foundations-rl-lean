import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Formalization.Probability.FiniteDistribution

/-! Basic finite distributions, discounted MDPs, and policies. -/
open scoped BigOperators
namespace StatisticalRL

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

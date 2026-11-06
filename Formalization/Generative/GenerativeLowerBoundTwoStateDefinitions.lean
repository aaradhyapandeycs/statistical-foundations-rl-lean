import Formalization.MDP.CoreDefinitions

/-!
Definitions only: the source two-state, one-action lower-bound MDP of
`chapters/generative_model_model_based.tex:1575–1633` (state `true` is `s₁`, state `false`
is the absorbing `s₂`). Facts about it are proved in `GenerativeLowerBoundTwoStateMDP.lean`.
-/

open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- The source transition: true is the rewarding state, false is absorbing. -/
noncomputable def hardRow (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : Bool) : FiniteDistribution Bool where
  prob t := if t then (if s then p else 0) else (if s then 1 - p else 1)
  prob_nonneg := by intro t; cases s <;> cases t <;> simp_all
  sum_prob := by cases s <;> simp

/-- Two-state source model with known deterministic rewards and one action. -/
noncomputable def hardMDP (γ p : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : DiscountedMDP Bool Unit where
  state_nonempty := inferInstance
  action_nonempty := inferInstance
  transition s _ := hardRow p hp hp1 s
  reward s _ := if s then 1 else 0
  reward_nonneg := by intro s a; cases s <;> simp
  reward_le_one := by intro s a; cases s <;> simp
  discount := γ
  discount_nonneg := hγ
  discount_lt_one := hγ1

end StatisticalRL.GenerativeLowerBound

import Formalization.MDP.CoreDefinitions
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# The hard MDP of the Q-learning lower bound (definitions only)

`M_hard` of `chapters/generative_model_model_free.tex:2735–2781`: states `{0,1,2,3}`, with
`p = (4γ-1)/(3γ)` (`defn-parameter-p-Q-lower`). The source lets action sets vary by state
(`A₁ = {1,2}`, all others `{1}`). Here every state has the two actions `Bool`; at states 0, 2
and 3 both actions are copies of the source's single action, and at state 1 they are the two
(identical) source actions. Rewards and transitions do not depend on the action.
-/

open scoped BigOperators
namespace StatisticalRL.QLearning

/-- The source parameter `p = (4γ-1)/(3γ)`. -/
noncomputable def qHardP (γ : ℝ) : ℝ := (4 * γ - 1) / (3 * γ)

/-- Transition rows of `M_hard`: states 0 and 3 are absorbing; from states 1 and 2 the
process stays with probability `p` and moves to 0 with probability `1-p`. -/
noncomputable def qHardRow (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Fin 4) :
    FiniteDistribution (Fin 4) where
  prob t :=
    if s = 0 then (if t = 0 then 1 else 0)
    else if s = 3 then (if t = 3 then 1 else 0)
    else if t = s then p else if t = 0 then 1 - p else 0
  prob_nonneg := by
    intro t
    fin_cases s <;> fin_cases t <;> simp <;> linarith
  sum_prob := by
    fin_cases s <;> simp [Fin.sum_univ_four]

/-- `M_hard` for `1/4 < γ < 1` (so that `0 < p < 1`); reward 0 at state 0 and 1 elsewhere. -/
noncomputable def qHardMDP (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) :
    DiscountedMDP (Fin 4) Bool where
  state_nonempty := ⟨0⟩
  action_nonempty := ⟨false⟩
  transition s _ := qHardRow (qHardP γ)
    (by unfold qHardP; apply div_nonneg <;> linarith)
    (by unfold qHardP; rw [div_le_one (by linarith)]; linarith) s
  reward s _ := if s = 0 then 0 else 1
  reward_nonneg := by intro s a; split <;> norm_num
  reward_le_one := by intro s a; split <;> norm_num
  discount := γ
  discount_nonneg := by linarith
  discount_lt_one := hγ1

end StatisticalRL.QLearning

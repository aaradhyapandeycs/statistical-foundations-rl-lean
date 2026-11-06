import Formalization.MDP.ForcedPrefixBridge
import Formalization.MDP.OptimalTrajectoryValue
import Formalization.MDP.FixedPoint

/-!
# State relabeling of finite discounted MDPs

Transport of a discounted MDP along a bijection of state carriers `e : σ ≃ τ`.
The relabeled model reads rewards, transitions and the discount through `e`;
actions are unchanged. Its Bellman fixed points, its actual forced-first-action
trajectory Q-functions and its optimal trajectory Q-function are those of the
original model read through `e`, and supremum-norm losses are unchanged.
-/

open scoped BigOperators

namespace StatisticalRL

namespace FiniteDistribution

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

/-- Push a finite probability vector forward along a bijection of carriers. -/
def relabel (d : FiniteDistribution Ω) (e : Ω ≃ Ξ) : FiniteDistribution Ξ where
  prob t := d.prob (e.symm t)
  prob_nonneg t := d.prob_nonneg (e.symm t)
  sum_prob := by
    rw [Equiv.sum_comp e.symm d.prob]
    exact d.sum_prob

@[simp]
theorem relabel_prob (d : FiniteDistribution Ω) (e : Ω ≃ Ξ) (t : Ξ) :
    (d.relabel e).prob t = d.prob (e.symm t) := rfl

/-- Expectation under the relabeled vector is expectation of the pulled-back function. -/
theorem expectation_relabel (d : FiniteDistribution Ω) (e : Ω ≃ Ξ) (V : Ξ → ℝ) :
    (d.relabel e).expectation V = d.expectation (fun s ↦ V (e s)) := by
  unfold expectation
  exact Fintype.sum_equiv e.symm _ _ (fun t ↦ by simp [relabel])

end FiniteDistribution

/-- Relabeling a supremum norm along a bijection of the index type leaves it unchanged. -/
theorem norm_comp_equiv_symm {σ τ β : Type*} [Fintype σ] [Fintype τ]
    [SeminormedAddCommGroup β] (e : σ ≃ τ) (F : σ → β) :
    ‖(fun t ↦ F (e.symm t))‖ = ‖F‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg F)).2 fun t ↦ norm_le_pi_norm F (e.symm t)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun s ↦ ?_
    simpa only [Equiv.symm_apply_apply] using norm_le_pi_norm (fun t ↦ F (e.symm t)) (e s)

namespace DiscountedMDP

variable {σ τ Action : Type*} [Fintype σ] [Fintype τ] [Fintype Action]

/-- The same MDP with states renamed by `e`; actions, rewards and discount are unchanged. -/
def relabelStates (M : DiscountedMDP σ Action) (e : σ ≃ τ) : DiscountedMDP τ Action where
  state_nonempty := M.state_nonempty.map e
  action_nonempty := M.action_nonempty
  transition t a := (M.transition (e.symm t) a).relabel e
  reward t a := M.reward (e.symm t) a
  reward_nonneg t a := M.reward_nonneg (e.symm t) a
  reward_le_one t a := M.reward_le_one (e.symm t) a
  discount := M.discount
  discount_nonneg := M.discount_nonneg
  discount_lt_one := M.discount_lt_one

@[simp]
theorem relabelStates_reward (M : DiscountedMDP σ Action) (e : σ ≃ τ) (t : τ) (a : Action) :
    (M.relabelStates e).reward t a = M.reward (e.symm t) a := rfl

@[simp]
theorem relabelStates_discount (M : DiscountedMDP σ Action) (e : σ ≃ τ) :
    (M.relabelStates e).discount = M.discount := rfl

@[simp]
theorem relabelStates_transition (M : DiscountedMDP σ Action) (e : σ ≃ τ) (t : τ)
    (a : Action) : (M.relabelStates e).transition t a = (M.transition (e.symm t) a).relabel e :=
  rfl

/-- The policy Bellman operator commutes with relabeling. -/
theorem relabelStates_qBellman (M : DiscountedMDP σ Action) (e : σ ≃ τ)
    (π : StationaryPolicy τ Action) (Q : τ → Action → ℝ) (t : τ) (a : Action) :
    (M.relabelStates e).qBellman π Q t a =
      M.qBellman (fun s ↦ π (e s)) (fun s ↦ Q (e s)) (e.symm t) a := by
  unfold qBellman
  rw [relabelStates_transition, FiniteDistribution.expectation_relabel]
  rfl

/-- The optimality Bellman operator commutes with relabeling. -/
theorem relabelStates_qOptimality (M : DiscountedMDP σ Action) (e : σ ≃ τ)
    (Q : τ → Action → ℝ) (t : τ) (a : Action) :
    (M.relabelStates e).qOptimality Q t a = M.qOptimality (fun s ↦ Q (e s)) (e.symm t) a := by
  unfold qOptimality
  rw [relabelStates_transition, FiniteDistribution.expectation_relabel]
  rfl

/-- The optimality fixed point of the relabeled model is the relabeled fixed point. -/
theorem relabelStates_optimalityFixedPoint (M : DiscountedMDP σ Action) (e : σ ≃ τ) :
    (M.relabelStates e).optimalityFixedPoint =
      fun t a ↦ M.optimalityFixedPoint (e.symm t) a := by
  symm
  apply ((M.relabelStates e).optimalityFixedPoint_characterization _).mp
  funext t a
  rw [relabelStates_qOptimality]
  simp only [Equiv.symm_apply_apply]
  exact congrFun (congrFun M.optimalityFixedPoint_spec (e.symm t)) a

/-- The policy fixed point of the relabeled model is the relabeled fixed point of the
pulled-back policy. -/
theorem relabelStates_policyFixedPoint (M : DiscountedMDP σ Action) (e : σ ≃ τ)
    (π : StationaryPolicy τ Action) :
    (M.relabelStates e).policyFixedPoint π =
      fun t a ↦ M.policyFixedPoint (fun s ↦ π (e s)) (e.symm t) a := by
  symm
  apply ((M.relabelStates e).policyFixedPoint_characterization π _).mp
  funext t a
  rw [relabelStates_qBellman]
  simp only [Equiv.symm_apply_apply]
  exact congrFun (congrFun (M.policyFixedPoint_spec _) (e.symm t)) a

/-- Actual forced-first-action trajectory Q of the relabeled model. -/
theorem relabelStates_trajectoryExpectedQ (M : DiscountedMDP σ Action) (e : σ ≃ τ)
    (π : StationaryPolicy τ Action) (t : τ) (a : Action) :
    (M.relabelStates e).trajectoryExpectedQ π t a =
      M.trajectoryExpectedQ (fun s ↦ π (e s)) (e.symm t) a := by
  rw [trajectoryExpectedQ_eq_policyFixedPoint, trajectoryExpectedQ_eq_policyFixedPoint,
    relabelStates_policyFixedPoint]

/-- Actual optimal trajectory Q of the relabeled model (independent of greedy tie choices). -/
theorem relabelStates_trajectoryExpectedQ_optimalGreedy (M : DiscountedMDP σ Action)
    (e : σ ≃ τ) (t : τ) (a : Action) :
    (M.relabelStates e).trajectoryExpectedQ (M.relabelStates e).optimalGreedyPolicy t a =
      M.trajectoryExpectedQ M.optimalGreedyPolicy (e.symm t) a := by
  rw [trajectoryExpectedQ_eq_policyFixedPoint, trajectoryExpectedQ_eq_policyFixedPoint,
    policyFixedPoint_optimalGreedy, policyFixedPoint_optimalGreedy,
    relabelStates_optimalityFixedPoint]

/-- The policy Q-loss in supremum norm is invariant under relabeling. -/
theorem relabelStates_policy_Q_loss_norm (M : DiscountedMDP σ Action) (e : σ ≃ τ)
    (π : StationaryPolicy τ Action) :
    ‖(M.relabelStates e).trajectoryExpectedQ π -
        (M.relabelStates e).trajectoryExpectedQ (M.relabelStates e).optimalGreedyPolicy‖ =
      ‖M.trajectoryExpectedQ (fun s ↦ π (e s)) - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ := by
  rw [← norm_comp_equiv_symm e
    (M.trajectoryExpectedQ (fun s ↦ π (e s)) - M.trajectoryExpectedQ M.optimalGreedyPolicy)]
  congr 1
  funext t a
  rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply,
    relabelStates_trajectoryExpectedQ_optimalGreedy, relabelStates_trajectoryExpectedQ]

/-- The Q-estimation error in supremum norm is invariant under relabeling. -/
theorem relabelStates_estimate_Q_loss_norm (M : DiscountedMDP σ Action) (e : σ ≃ τ)
    (Qhat : τ → Action → ℝ) :
    ‖Qhat - (M.relabelStates e).trajectoryExpectedQ (M.relabelStates e).optimalGreedyPolicy‖ =
      ‖(fun s ↦ Qhat (e s)) - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ := by
  rw [← norm_comp_equiv_symm e
    ((fun s ↦ Qhat (e s)) - M.trajectoryExpectedQ M.optimalGreedyPolicy)]
  congr 1
  funext t a
  simp only [Pi.sub_apply, relabelStates_trajectoryExpectedQ_optimalGreedy,
    Equiv.apply_symm_apply]

end DiscountedMDP

end StatisticalRL

import Formalization.MDP.FixedPoint
import Formalization.MDP.FiniteOptimal
import Mathlib.Tactic.FieldSimp

/-!
# A one-state Bellman obstruction

With one state and known rewards, the optimality Bellman fixed point is
computable exactly without transition samples. This concerns the project's
Bellman fixed points; identification with infinite trajectory Q-values and a
statistical lower-bound experiment remain separate obligations.
-/

namespace StatisticalRL.Obstructions

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The maximum of a finite family shifts by the same additive constant. -/
theorem actionMaximum_add_const [Nonempty Action] (f : Action → ℝ) (c : ℝ) :
    actionMaximum (fun a ↦ f a + c) = actionMaximum f + c := by
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
    intro a _
    exact add_le_add (le_actionMaximum f a) le_rfl
  · obtain ⟨a, ha⟩ := EnvironmentStage.exists_maximizer f
    rw [← ha]
    exact le_actionMaximum (fun b ↦ f b + c) a

/-- The formula is a function only of the known reward and discount. -/
noncomputable def oneStateQ (M : DiscountedMDP State Action) (s : State) (a : Action) : ℝ :=
  letI : Nonempty Action := M.action_nonempty
  M.reward s a + M.discount * actionMaximum (M.reward s) / (1 - M.discount)

/-- The estimator does not depend on the transition kernel or reward bounds. -/
theorem oneStateQ_eq_of_reward_discount_eq (M N : DiscountedMDP State Action)
    (hreward : M.reward = N.reward) (hdiscount : M.discount = N.discount) :
    oneStateQ M = oneStateQ N := by
  funext s a
  simp only [oneStateQ, hreward, hdiscount]

/-- The explicit one-state formula satisfies the actual optimality Bellman equation. -/
theorem oneStateQ_qOptimality [Subsingleton State] (M : DiscountedMDP State Action) :
    M.qOptimality (oneStateQ M) = oneStateQ M := by
  letI : Nonempty Action := M.action_nonempty
  funext s a
  have hconst : (fun t ↦ actionMaximum (oneStateQ M t)) =
      (fun _ ↦ actionMaximum (oneStateQ M s)) := by
    funext t
    rw [Subsingleton.elim t s]
  have hmax : actionMaximum (oneStateQ M s) =
      actionMaximum (M.reward s) +
        M.discount * actionMaximum (M.reward s) / (1 - M.discount) := by
    exact actionMaximum_add_const (M.reward s) _
  change M.reward s a + M.discount *
    (M.transition s a).expectation (fun t ↦ actionMaximum (oneStateQ M t)) = oneStateQ M s a
  rw [hconst, FiniteDistribution.expectation_const, hmax]
  unfold oneStateQ
  have hne : 1 - M.discount ≠ 0 := ne_of_gt (sub_pos.mpr M.discount_lt_one)
  field_simp
  ring

/-- Exact Bellman fixed point for every admissible one-state MDP. -/
theorem optimalityFixedPoint_eq_oneStateQ [Subsingleton State]
    (M : DiscountedMDP State Action) : M.optimalityFixedPoint = oneStateQ M := by
  exact ((M.optimalityFixedPoint_characterization (oneStateQ M)).mp
    (oneStateQ_qOptimality M)).symm

/-- Choose a reward-maximizing action using the known reward table. -/
noncomputable def oneStateGreedyAction (M : DiscountedMDP State Action) (s : State) : Action := by
  letI : Nonempty Action := M.action_nonempty
  exact Classical.choose (EnvironmentStage.exists_maximizer (M.reward s))

theorem oneStateGreedyAction_reward (M : DiscountedMDP State Action) (s : State) :
    M.reward s (oneStateGreedyAction M s) =
      letI : Nonempty Action := M.action_nonempty
      actionMaximum (M.reward s) := by
  letI : Nonempty Action := M.action_nonempty
  exact Classical.choose_spec (EnvironmentStage.exists_maximizer (M.reward s))

/-- A stationary deterministic policy, encoded as point masses. -/
noncomputable def oneStateGreedyPolicy (M : DiscountedMDP State Action) :
    StationaryPolicy State Action :=
  fun s ↦ EnvironmentStage.pointMass (oneStateGreedyAction M s)

/-- The greedy policy's Bellman Q fixed point agrees with the optimality fixed point. -/
theorem greedy_policyFixedPoint_eq_optimalityFixedPoint [Subsingleton State]
    (M : DiscountedMDP State Action) :
    M.policyFixedPoint (oneStateGreedyPolicy M) = M.optimalityFixedPoint := by
  letI : Nonempty Action := M.action_nonempty
  rw [optimalityFixedPoint_eq_oneStateQ M]
  symm
  apply (M.policyFixedPoint_characterization (oneStateGreedyPolicy M) (oneStateQ M)).mp
  funext s a
  have hconst : (fun t ↦ (oneStateGreedyPolicy M t).expectation (oneStateQ M t)) =
      (fun _ ↦ (oneStateGreedyPolicy M s).expectation (oneStateQ M s)) := by
    funext t
    rw [Subsingleton.elim t s]
  change M.reward s a + M.discount *
    (M.transition s a).expectation
      (fun t ↦ (oneStateGreedyPolicy M t).expectation (oneStateQ M t)) = oneStateQ M s a
  rw [hconst, FiniteDistribution.expectation_const]
  change M.reward s a + M.discount *
    (EnvironmentStage.pointMass (oneStateGreedyAction M s)).expectation (oneStateQ M s) = _
  rw [EnvironmentStage.expectation_pointMass]
  unfold oneStateQ
  rw [oneStateGreedyAction_reward]
  have hne : 1 - M.discount ≠ 0 := ne_of_gt (sub_pos.mpr M.discount_lt_one)
  field_simp
  ring

end StatisticalRL.Obstructions

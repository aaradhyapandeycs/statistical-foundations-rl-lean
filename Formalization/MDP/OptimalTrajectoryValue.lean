import Formalization.MDP.ForcedPrefixBridge
import Formalization.MDP.FiniteOptimal

/-!
# Optimal stationary policy for infinite trajectory Q and V

Construct a deterministic greedy stationary policy from the actual optimal
Bellman fixed point and compare it against every stationary randomized policy.
Source: arXiv:2610.41903v1, `eq:optimal-Vstar-Q-star-defn` and
`eq:bellman_fix_point`.
-/

open Filter
open scoped Topology

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- A genuine maximizing action for the optimality Bellman solution. -/
noncomputable def optimalGreedyAction (M : DiscountedMDP State Action) (s : State) : Action := by
  letI : Nonempty Action := M.action_nonempty
  exact Classical.choose (EnvironmentStage.exists_maximizer (M.optimalityFixedPoint s))

theorem optimalGreedyAction_max (M : DiscountedMDP State Action) (s : State) :
    M.optimalityFixedPoint s (M.optimalGreedyAction s) =
      letI : Nonempty Action := M.action_nonempty
      actionMaximum (M.optimalityFixedPoint s) := by
  letI : Nonempty Action := M.action_nonempty
  exact Classical.choose_spec (EnvironmentStage.exists_maximizer (M.optimalityFixedPoint s))

/-- The corresponding deterministic stationary policy. -/
noncomputable def optimalGreedyPolicy (M : DiscountedMDP State Action) :
    StationaryPolicy State Action := fun s ↦ EnvironmentStage.pointMass (M.optimalGreedyAction s)

/-- The greedy policy's Bellman operator agrees with the optimality operator
at the optimality solution. -/
theorem qBellman_optimalGreedy (M : DiscountedMDP State Action) :
    M.qBellman M.optimalGreedyPolicy M.optimalityFixedPoint = M.optimalityFixedPoint := by
  letI : Nonempty Action := M.action_nonempty
  have hopt := M.optimalityFixedPoint_spec
  funext s a
  have h := congrFun (congrFun hopt s) a
  change M.reward s a + M.discount *
    (M.transition s a).expectation (fun t ↦ actionMaximum (M.optimalityFixedPoint t)) =
      M.optimalityFixedPoint s a at h
  change M.reward s a + M.discount *
    (M.transition s a).expectation (fun t ↦
      (EnvironmentStage.pointMass (M.optimalGreedyAction t)).expectation
        (M.optimalityFixedPoint t)) = M.optimalityFixedPoint s a
  simp_rw [EnvironmentStage.expectation_pointMass, M.optimalGreedyAction_max]
  exact h

/-- The greedy policy's Q-Bellman solution is exactly the optimal solution. -/
theorem policyFixedPoint_optimalGreedy (M : DiscountedMDP State Action) :
    M.policyFixedPoint M.optimalGreedyPolicy = M.optimalityFixedPoint := by
  exact ((M.policyFixedPoint_characterization M.optimalGreedyPolicy _).mp
    M.qBellman_optimalGreedy).symm

/-- Bellman policy evaluation is monotone in its continuation Q. -/
theorem qBellman_monotone (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : Monotone (M.qBellman π) := by
  intro Q R h s a
  unfold qBellman
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ M.discount_nonneg
  apply (M.transition s a).expectation_mono
  intro t
  apply (π t).expectation_mono
  intro b
  exact h t b

/-- Every policy backup of the optimal fixed point is bounded by that point. -/
theorem qBellman_optimal_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    M.qBellman π M.optimalityFixedPoint ≤ M.optimalityFixedPoint := by
  letI : Nonempty Action := M.action_nonempty
  intro s a
  have hopt := congrFun (congrFun M.optimalityFixedPoint_spec s) a
  change M.reward s a + M.discount *
    (M.transition s a).expectation (fun t ↦ actionMaximum (M.optimalityFixedPoint t)) =
      M.optimalityFixedPoint s a at hopt
  rw [← hopt]
  unfold qBellman
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ M.discount_nonneg
  apply (M.transition s a).expectation_mono
  intro t
  exact (π t).expectation_le_const (fun b ↦ le_actionMaximum _ b)

/-- The optimal Bellman solution dominates the solution of any stationary
randomized policy. -/
theorem policyFixedPoint_le_optimal (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    M.policyFixedPoint π s a ≤ M.optimalityFixedPoint s a := by
  have hiter : ∀ n : ℕ, (M.qBellman π)^[n] M.optimalityFixedPoint ≤ M.optimalityFixedPoint := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (M.qBellman_monotone π ih).trans (M.qBellman_optimal_le π)
  have ht := (tendsto_pi_nhds.mp
    ((tendsto_pi_nhds.mp (M.tendsto_policy_evaluation_iteration π M.optimalityFixedPoint)) s)) a
  exact le_of_tendsto' ht (fun n ↦ hiter n s a)

/-- One deterministic policy simultaneously attains the optimality fixed point
as its actual forced-action infinite-trajectory Q. -/
theorem optimalGreedy_trajectoryQ (M : DiscountedMDP State Action) (s : State) (a : Action) :
    M.trajectoryExpectedQ M.optimalGreedyPolicy s a = M.optimalityFixedPoint s a := by
  rw [M.trajectoryExpectedQ_eq_policyFixedPoint, M.policyFixedPoint_optimalGreedy]

/-- The same greedy policy dominates all stationary randomized policies at
all states and all forced first actions, including zero-support actions. -/
theorem trajectoryQ_le_optimalGreedy (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    M.trajectoryExpectedQ π s a ≤ M.trajectoryExpectedQ M.optimalGreedyPolicy s a := by
  rw [M.trajectoryExpectedQ_eq_policyFixedPoint, M.optimalGreedy_trajectoryQ]
  exact M.policyFixedPoint_le_optimal π s a

/-- The same greedy policy also dominates all stationary randomized policies'
actual trajectory state values. -/
theorem trajectoryValue_le_optimalGreedy (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) :
    M.trajectoryExpectedValue π s ≤ M.trajectoryExpectedValue M.optimalGreedyPolicy s := by
  letI : Nonempty Action := M.action_nonempty
  calc
    M.trajectoryExpectedValue π s = (π s).expectation (M.trajectoryExpectedQ π s) :=
      M.trajectoryExpectedValue_eq_policyAverageQ π s
    _ ≤ (π s).expectation (M.optimalityFixedPoint s) := by
      apply (π s).expectation_mono
      intro a
      rw [M.trajectoryExpectedQ_eq_policyFixedPoint]
      exact M.policyFixedPoint_le_optimal π s a
    _ ≤ actionMaximum (M.optimalityFixedPoint s) :=
      (π s).expectation_le_const (fun a ↦ le_actionMaximum _ a)
    _ = M.trajectoryExpectedValue M.optimalGreedyPolicy s := by
      rw [M.trajectoryExpectedValue_eq_policyAverageQ]
      change actionMaximum (M.optimalityFixedPoint s) =
        (EnvironmentStage.pointMass (M.optimalGreedyAction s)).expectation
          (M.trajectoryExpectedQ M.optimalGreedyPolicy s)
      rw [EnvironmentStage.expectation_pointMass, M.optimalGreedy_trajectoryQ,
        M.optimalGreedyAction_max]

/-- A single deterministic stationary policy simultaneously dominates every
stationary randomized policy in both actual trajectory criteria. -/
theorem exists_stationary_trajectory_optimal (M : DiscountedMDP State Action) :
    ∃ f : State → Action, ∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
      M.trajectoryExpectedQ π s a ≤
        M.trajectoryExpectedQ (fun t ↦ EnvironmentStage.pointMass (f t)) s a ∧
      M.trajectoryExpectedValue π s ≤
        M.trajectoryExpectedValue (fun t ↦ EnvironmentStage.pointMass (f t)) s := by
  refine ⟨M.optimalGreedyAction, ?_⟩
  intro π s a
  exact ⟨M.trajectoryQ_le_optimalGreedy π s a, M.trajectoryValue_le_optimalGreedy π s⟩

end StatisticalRL.DiscountedMDP

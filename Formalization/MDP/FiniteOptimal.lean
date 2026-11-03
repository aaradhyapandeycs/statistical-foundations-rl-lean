import Formalization.MDP.FiniteQTrajectory

/-!
# Finite-horizon optimality

A stage of the environment contains transitions and rewards independently of
any policy. Backward induction constructs a deterministic decision rule for
all states at every remaining stage. Its actual trajectory values dominate
those of every nonstationary randomized Markov policy in the same environment.

Source: Chapter 2, Section 2.2 of arXiv:2610.41903v1,
`eq:defn-optimalV-optimalQ-finite-prelim` and `eq:Bellman-finite-opt`.
-/

open scoped BigOperators

namespace StatisticalRL

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- One time step of an environment, before any policy is selected. -/
structure EnvironmentStage (State Action : Type*) [Fintype State] [Fintype Action] where
  state_nonempty : Nonempty State
  action_nonempty : Nonempty Action
  transition : State → Action → FiniteDistribution State
  reward : State → Action → ℝ
  reward_nonneg : ∀ s a, 0 ≤ reward s a
  reward_le_one : ∀ s a, reward s a ≤ 1

namespace EnvironmentStage

/-- Attach a decision rule without changing the environment. -/
def withPolicy (e : EnvironmentStage State Action) (π : StationaryPolicy State Action) :
    DecisionStage State Action where
  state_nonempty := e.state_nonempty
  action_nonempty := e.action_nonempty
  transition := e.transition
  reward := e.reward
  reward_nonneg := e.reward_nonneg
  reward_le_one := e.reward_le_one
  policy := π

/-- An actual nonstationary randomized policy indexed from the current stage. -/
def controlled : List (EnvironmentStage State Action) →
    (ℕ → StationaryPolicy State Action) → List (DecisionStage State Action)
  | [], _ => []
  | e :: es, π => e.withPolicy (π 0) :: controlled es (fun n ↦ π (n + 1))

/-- Expected one-step reward and continuation in the policy-independent model. -/
def qBackup (e : EnvironmentStage State Action) (V : State → ℝ)
    (s : State) (a : Action) : ℝ :=
  e.reward s a + (e.transition s a).expectation V

/-- Optimal continuation value, defined by backward induction. -/
noncomputable def optimalValue : List (EnvironmentStage State Action) → State → ℝ
  | [] => fun _ ↦ 0
  | e :: es => fun s ↦
    letI : Nonempty Action := e.action_nonempty
    actionMaximum (e.qBackup (optimalValue es) s)

/-- Optimal action-value, including the source's zero terminal convention. -/
noncomputable def optimalQ : List (EnvironmentStage State Action) → State → Action → ℝ
  | [] => fun _ _ ↦ 0
  | e :: es => e.qBackup (optimalValue es)

/-- A maximizing action exists in the finite nonempty action space. -/
theorem exists_maximizer [Nonempty Action] (f : Action → ℝ) :
    ∃ a, f a = actionMaximum f := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  exact ⟨a, ha.symm⟩

/-- A maximizing action in each state of a stage. -/
noncomputable def greedyAction (e : EnvironmentStage State Action)
    (V : State → ℝ) (s : State) : Action := by
  letI : Nonempty Action := e.action_nonempty
  exact Classical.choose (exists_maximizer (e.qBackup V s))

theorem greedyAction_max (e : EnvironmentStage State Action) (V : State → ℝ)
    (s : State) :
    e.qBackup V s (e.greedyAction V s) =
      letI : Nonempty Action := e.action_nonempty
      actionMaximum (e.qBackup V s) := by
  letI : Nonempty Action := e.action_nonempty
  exact Classical.choose_spec (exists_maximizer (e.qBackup V s))

/-- The probability vector concentrated on a specified action. -/
noncomputable def pointMass (a : Action) : FiniteDistribution Action := by
  classical
  exact ⟨fun b ↦ if b = a then 1 else 0,
    fun b ↦ by dsimp; split <;> norm_num,
    by simp⟩

@[simp]
theorem expectation_pointMass (a : Action) (f : Action → ℝ) :
    (pointMass a).expectation f = f a := by
  classical
  simp [pointMass, FiniteDistribution.expectation]

/-- The greedy policy at each stage depends on that stage's optimal continuation. -/
noncomputable def greedyStages : List (EnvironmentStage State Action) →
    List (DecisionStage State Action)
  | [] => []
  | e :: es => e.withPolicy (fun s ↦ pointMass (e.greedyAction (optimalValue es) s)) ::
      greedyStages es

/-- The constructed deterministic policy realizes the backward optimal value
as the expectation of actual cumulative trajectory reward. -/
theorem greedy_trajectoryValue (es : List (EnvironmentStage State Action)) (s : State) :
    DecisionStage.trajectoryValue (greedyStages es) s = optimalValue es s := by
  induction es generalizing s with
  | nil => exact DecisionStage.trajectoryValue_nil s
  | cons e es ih =>
    rw [greedyStages, DecisionStage.trajectoryValue_cons]
    change (pointMass (e.greedyAction (optimalValue es) s)).expectation
      (fun a ↦ e.qBackup (DecisionStage.trajectoryValue (greedyStages es)) s a) = _
    rw [expectation_pointMass]
    rw [show DecisionStage.trajectoryValue (greedyStages es) = optimalValue es from funext ih]
    exact e.greedyAction_max (optimalValue es) s

/-- Every randomized nonstationary policy's actual trajectory return is bounded
by the common environment's backward optimal value. -/
theorem trajectoryValue_le_optimal (es : List (EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (s : State) :
    DecisionStage.trajectoryValue (controlled es π) s ≤ optimalValue es s := by
  induction es generalizing π s with
  | nil => simp [controlled, optimalValue]
  | cons e es ih =>
    rw [controlled, DecisionStage.trajectoryValue_cons]
    change (π 0 s).expectation
      (fun a ↦ e.qBackup (DecisionStage.trajectoryValue (controlled es (fun n ↦ π (n + 1)))) s a) ≤ _
    letI : Nonempty Action := e.action_nonempty
    change _ ≤ actionMaximum (e.qBackup (optimalValue es) s)
    apply (π 0 s).expectation_le_const
    intro a
    calc
      e.qBackup (DecisionStage.trajectoryValue (controlled es (fun n ↦ π (n + 1)))) s a ≤
          e.qBackup (optimalValue es) s a := by
        unfold qBackup
        apply add_le_add_right
        exact (e.transition s a).expectation_mono (fun t ↦ ih _ t)
      _ ≤ actionMaximum (e.qBackup (optimalValue es) s) := le_actionMaximum _ _

/-- The same single greedy stage sequence dominates all randomized policies. -/
theorem greedy_dominates (es : List (EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (s : State) :
    DecisionStage.trajectoryValue (controlled es π) s ≤
      DecisionStage.trajectoryValue (greedyStages es) s := by
  rw [greedy_trajectoryValue]
  exact trajectoryValue_le_optimal es π s

/-- The greedy policy's action-conditioned trajectory return realizes optimal Q. -/
theorem greedy_trajectoryQ (es : List (EnvironmentStage State Action))
    (s : State) (a : Action) :
    DecisionStage.trajectoryQ (greedyStages es) s a = optimalQ es s a := by
  cases es with
  | nil => rfl
  | cons e es =>
    rw [greedyStages, DecisionStage.trajectoryQ_cons]
    change e.qBackup (DecisionStage.trajectoryValue (greedyStages es)) s a = _
    rw [show DecisionStage.trajectoryValue (greedyStages es) = optimalValue es from
      funext (greedy_trajectoryValue es)]
    rfl

/-- The action-conditioned return of any policy is also dominated at all
state-action pairs, including actions that policy would not select. -/
theorem trajectoryQ_le_optimal (es : List (EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (s : State) (a : Action) :
    DecisionStage.trajectoryQ (controlled es π) s a ≤ optimalQ es s a := by
  cases es with
  | nil => exact le_refl 0
  | cons e es =>
    rw [controlled, DecisionStage.trajectoryQ_cons]
    change e.qBackup (DecisionStage.trajectoryValue (controlled es (fun n ↦ π (n + 1)))) s a ≤
      e.qBackup (optimalValue es) s a
    unfold qBackup
    apply add_le_add_right
    exact (e.transition s a).expectation_mono (fun t ↦ trajectoryValue_le_optimal _ _ t)

/-- Finite optimality Bellman equations, with a common nonstationary stage. -/
theorem optimal_bellman (e : EnvironmentStage State Action)
    (es : List (EnvironmentStage State Action)) (s : State) (a : Action) :
    optimalQ (e :: es) s a = e.reward s a + (e.transition s a).expectation (optimalValue es) ∧
    optimalValue (e :: es) s =
      letI : Nonempty Action := e.action_nonempty
      actionMaximum (optimalQ (e :: es) s) := by
  exact ⟨rfl, rfl⟩

/-- Taking a suffix preserves the very same greedy decisions. -/
theorem greedyStages_drop (es : List (EnvironmentStage State Action)) (n : ℕ) :
    (greedyStages es).drop n = greedyStages (es.drop n) := by
  induction n generalizing es with
  | zero => simp
  | succ n ih =>
    cases es with
    | nil => rfl
    | cons e es => simpa only [greedyStages, List.drop_succ_cons] using ih es

/-- The suffix of a policy-controlled episode uses that same policy at later times. -/
theorem controlled_drop (es : List (EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (n : ℕ) :
    (controlled es π).drop n = controlled (es.drop n) (fun k ↦ π (n + k)) := by
  induction n generalizing es π with
  | zero => simp
  | succ n ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      simpa only [controlled, List.drop_succ_cons, Nat.succ_add, Nat.add_succ] using
        ih es (fun k ↦ π (k + 1))

/-- One greedy policy simultaneously dominates each suffix of any one
nonstationary randomized policy, at every state and action. -/
theorem greedy_suffix_dominates (es : List (EnvironmentStage State Action))
    (π : ℕ → StationaryPolicy State Action) (n : ℕ) (s : State) (a : Action) :
    DecisionStage.trajectoryValue ((controlled es π).drop n) s ≤
        DecisionStage.trajectoryValue ((greedyStages es).drop n) s ∧
    DecisionStage.trajectoryQ ((controlled es π).drop n) s a ≤
        DecisionStage.trajectoryQ ((greedyStages es).drop n) s a := by
  rw [controlled_drop, greedyStages_drop, greedy_trajectoryValue, greedy_trajectoryQ]
  exact ⟨trajectoryValue_le_optimal _ _ _, trajectoryQ_le_optimal _ _ _ _⟩

/-- Optimal state value at source time `i + 1`, including terminal time. -/
noncomputable def optimalValueAt (es : List (EnvironmentStage State Action))
    (i : Fin (es.length + 1)) : State → ℝ := optimalValue (es.drop i.val)

/-- Optimal action value at source time `i + 1`, including terminal time. -/
noncomputable def optimalQAt (es : List (EnvironmentStage State Action))
    (i : Fin (es.length + 1)) : State → Action → ℝ := optimalQ (es.drop i.val)

@[simp]
theorem optimalValueAt_terminal (es : List (EnvironmentStage State Action)) (s : State) :
    optimalValueAt es (Fin.last es.length) s = 0 := by
  simp [optimalValueAt, optimalValue]

@[simp]
theorem optimalQAt_terminal (es : List (EnvironmentStage State Action))
    (s : State) (a : Action) : optimalQAt es (Fin.last es.length) s a = 0 := by
  simp [optimalQAt, optimalQ]

/-- Each suffix of the one greedy policy realizes the corresponding optimal value. -/
theorem greedy_suffix_value (es : List (EnvironmentStage State Action)) (n : ℕ) (s : State) :
    DecisionStage.trajectoryValue ((greedyStages es).drop n) s = optimalValue (es.drop n) s := by
  rw [greedyStages_drop, greedy_trajectoryValue]

/-- Each suffix of the same greedy policy realizes optimal action values as well. -/
theorem greedy_suffix_Q (es : List (EnvironmentStage State Action)) (n : ℕ)
    (s : State) (a : Action) :
    DecisionStage.trajectoryQ ((greedyStages es).drop n) s a = optimalQ (es.drop n) s a := by
  rw [greedyStages_drop, greedy_trajectoryQ]

/-- Optimal Bellman equations at each nonterminal time. -/
theorem optimalAt_bellman (es : List (EnvironmentStage State Action))
    (i : Fin es.length) (s : State) (a : Action) :
    optimalQAt es i.castSucc s a = (es.get i).reward s a +
      ((es.get i).transition s a).expectation (optimalValueAt es i.succ) ∧
    optimalValueAt es i.castSucc s =
      letI : Nonempty Action := (es.get i).action_nonempty
      actionMaximum (optimalQAt es i.castSucc s) := by
  change optimalQ (es.drop i.val) s a = (es.get i).reward s a +
      ((es.get i).transition s a).expectation (optimalValue (es.drop (i.val + 1))) ∧
    optimalValue (es.drop i.val) s =
      letI : Nonempty Action := (es.get i).action_nonempty
      actionMaximum (optimalQ (es.drop i.val) s)
  rw [List.drop_eq_getElem_cons i.isLt]
  exact optimal_bellman _ _ _ _

end EnvironmentStage
end StatisticalRL

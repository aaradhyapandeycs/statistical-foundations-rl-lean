import Formalization.MDP.FiniteOccupancy
import Formalization.MDP.FiniteOptimal

/-!
# Full-episode occupancy events

The recorded action and state at each genuine stage are read directly from the
single full-episode trajectory. Their event probabilities marginalize all
later actions and states. Source: `eq:dh-pi-defn` and `eq:dhstar-finite`.
-/

open scoped BigOperators

namespace StatisticalRL.DecisionStage

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- State before the indexed action on a complete trajectory. -/
def pathState : (n : ℕ) → Fin n → State → FinitePath State Action n → State
  | 0, i, _, _ => Fin.elim0 i
  | n + 1, i, s, path =>
      Fin.cases s (fun j ↦ pathState n j path.2.1 path.2.2) i

/-- Action at an indexed decision on a complete trajectory. -/
def pathAction : (n : ℕ) → Fin n → FinitePath State Action n → Action
  | 0, i, _ => Fin.elim0 i
  | n + 1, i, path =>
      Fin.cases path.1 (fun j ↦ pathAction n j path.2.2) i

/-- Arbitrary functions of the state at a decision have the same expectation
under the complete path and under the recursively propagated state law. -/
theorem fullPath_state_expectation (stages : List (DecisionStage State Action))
    (ρ : FiniteDistribution State) (i : Fin stages.length) (f : State → ℝ) :
    ρ.expectation (fun x ↦ (trajectoryLaw stages x).expectation
      (fun path ↦ f (pathState stages.length i x path))) =
    (stateAfter (stages.take i.val) ρ).expectation f := by
  induction stages generalizing ρ with
  | nil => exact Fin.elim0 i
  | cons stage tail ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [pathState, stateAfter, FiniteDistribution.expectation_const]
    · simp only [Fin.val_succ, List.take_succ_cons, stateAfter]
      rw [← ih _ j]
      simp_rw [FiniteDistribution.expectation_bind, trajectoryExpectation_cons]
      rfl

/-- Arbitrary functions of the state and action at a decision have the same
expectation under the complete path and the forward state law and policy. -/
theorem fullPath_joint_expectation (stages : List (DecisionStage State Action))
    (ρ : FiniteDistribution State) (i : Fin stages.length) (f : State → Action → ℝ) :
    ρ.expectation (fun x ↦ (trajectoryLaw stages x).expectation
      (fun path ↦ f (pathState stages.length i x path) (pathAction stages.length i path))) =
    (stateAfter (stages.take i.val) ρ).expectation (fun x ↦
      ((stages.get i).policy x).expectation (f x)) := by
  induction stages generalizing ρ with
  | nil => exact Fin.elim0 i
  | cons stage tail ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.val_zero, List.take_zero, stateAfter, List.get_eq_getElem,
        List.getElem_cons_zero]
      simp_rw [trajectoryExpectation_cons]
      simp [pathState, pathAction, FiniteDistribution.expectation_const]
    · simp only [Fin.val_succ, List.take_succ_cons, stateAfter, List.get_eq_getElem,
        List.getElem_cons_succ]
      change _ = (stateAfter (tail.take j.val)
        (ρ.bind (fun s ↦ (stage.policy s).bind (stage.transition s)))).expectation
          (fun x ↦ ((tail.get j).policy x).expectation (f x))
      rw [← ih _ j]
      simp_rw [FiniteDistribution.expectation_bind, trajectoryExpectation_cons]
      rfl

noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- State occupancy is the state event under the complete episode trajectory. -/
theorem stateOccupancy_eq_fullPath (stages : List (DecisionStage State Action))
    (ρ : FiniteDistribution State) (i : Fin stages.length) (s : State) :
    stateOccupancy stages ρ i s =
      ρ.expectation (fun x ↦ (trajectoryLaw stages x).expectation
        (fun path ↦ if pathState stages.length i x path = s then 1 else 0)) := by
  rw [fullPath_state_expectation stages ρ i (fun x ↦ if x = s then 1 else 0)]
  classical
  simp [stateOccupancy, FiniteDistribution.expectation]

/-- Joint occupancy is the state-action event under the complete episode. -/
theorem stateActionOccupancy_eq_fullPath (stages : List (DecisionStage State Action))
    (ρ : FiniteDistribution State) (i : Fin stages.length) (s : State) (a : Action) :
    stateActionOccupancy stages ρ i s a =
      ρ.expectation (fun x ↦ (trajectoryLaw stages x).expectation
        (fun path ↦ if pathState stages.length i x path = s ∧
          pathAction stages.length i path = a then 1 else 0)) := by
  rw [fullPath_joint_expectation stages ρ i (fun x b ↦ if x = s ∧ b = a then 1 else 0),
    stateActionOccupancy_eq]
  classical
  simp only [FiniteDistribution.expectation]
  have inner (x : State) :
      (∑ b, ((stages.get i).policy x).prob b * (if x = s ∧ b = a then 1 else 0)) =
        if x = s then ((stages.get i).policy x).prob a else 0 := by
    by_cases h : x = s
    · simp [h]
    · simp [h]
  simp_rw [inner]
  simp [stateOccupancy]

end StatisticalRL.DecisionStage

namespace StatisticalRL.EnvironmentStage

variable {State Action : Type*} [Fintype State] [Fintype Action]

@[simp] theorem greedyStages_length (es : List (EnvironmentStage State Action)) :
    (greedyStages es).length = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [greedyStages, ih]

/-- The same genuine decision index in the constructed greedy stage list. -/
def greedyIndex (es : List (EnvironmentStage State Action)) (i : Fin es.length) :
    Fin (greedyStages es).length := ⟨i.val, by simp [i.isLt]⟩

/-- The deterministic optimal action at the indexed state and stage. -/
noncomputable def greedyActionAt (es : List (EnvironmentStage State Action))
    (i : Fin es.length) (s : State) : Action :=
  (es.get i).greedyAction (optimalValue (es.drop (i.val + 1))) s

/-- The policy stored at each greedy stage is the point mass of that same
indexed greedy action. -/
theorem greedyStages_policy_at (es : List (EnvironmentStage State Action))
    (i : Fin es.length) (s : State) :
    ((greedyStages es).get (greedyIndex es i)).policy s = pointMass (greedyActionAt es i s) := by
  induction es with
  | nil => exact Fin.elim0 i
  | cons e es ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · simpa [greedyIndex, greedyActionAt, greedyStages, List.drop_succ_cons] using ih j

noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- Optimal deterministic state-action occupancy is its state occupancy times
the indicator of the greedy action, as in `eq:dhstar-finite`. -/
theorem greedy_stateActionOccupancy (es : List (EnvironmentStage State Action))
    (ρ : FiniteDistribution State) (i : Fin es.length) (s : State) (a : Action) :
    DecisionStage.stateActionOccupancy (greedyStages es) ρ (greedyIndex es i) s a =
      DecisionStage.stateOccupancy (greedyStages es) ρ (greedyIndex es i) s *
        (if a = greedyActionAt es i s then 1 else 0) := by
  rw [DecisionStage.stateActionOccupancy_eq, greedyStages_policy_at]
  rfl

end StatisticalRL.EnvironmentStage

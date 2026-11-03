import Formalization.MDP.FiniteQTrajectory

/-!
# Finite-horizon occupancy probabilities

The state law is generated forward from the initial distribution by the
actual action and transition kernels. The state-action probability is an
event probability under a one-step trajectory law sampled from that state law.
The index `i` corresponds to the paper's `h = i + 1`.
Source: Chapter 2, `eq:dh-pi-defn` and `eqn:defn-d1rho-finite`.
-/

open scoped BigOperators

namespace StatisticalRL.DecisionStage

variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- Forward state law after the given (possibly empty) prefix of stages. -/
def stateAfter : List (DecisionStage State Action) → FiniteDistribution State →
    FiniteDistribution State
  | [], ρ => ρ
  | stage :: tail, ρ =>
      stateAfter tail (ρ.bind (fun s ↦ (stage.policy s).bind (stage.transition s)))

/-- The state reached after all actions and transitions in a finite path. -/
def finalState : (n : ℕ) → State → FinitePath State Action n → State
  | 0, s, _ => s
  | n + 1, _, path => finalState n path.2.1 path.2.2

/-- Forward propagation is exactly the final-state marginal of the separately
constructed trajectory law, mixed over the initial distribution. -/
theorem stateAfter_expectation_eq_trajectory
    (stages : List (DecisionStage State Action)) (ρ : FiniteDistribution State)
    (f : State → ℝ) :
    (stateAfter stages ρ).expectation f =
      ρ.expectation (fun s ↦ (trajectoryLaw stages s).expectation
        (fun path ↦ f (finalState stages.length s path))) := by
  induction stages generalizing ρ with
  | nil =>
    simp [stateAfter, FiniteDistribution.expectation, trajectoryLaw, pathWeight,
      FinitePath, finalState]
  | cons stage tail ih =>
    rw [stateAfter, ih, FiniteDistribution.expectation_bind]
    simp_rw [FiniteDistribution.expectation_bind, trajectoryExpectation_cons]
    rfl

/-- State occupancy at a genuine decision time. -/
def stateOccupancy (stages : List (DecisionStage State Action))
    (ρ : FiniteDistribution State) (i : Fin stages.length) (s : State) : ℝ :=
  (stateAfter (stages.take i.val) ρ).prob s

/-- Joint occupancy is the probability of the state-action event in the
one-stage trajectory sampled from the forward state law. -/
noncomputable def stateActionOccupancy (stages : List (DecisionStage State Action))
    (ρ : FiniteDistribution State) (i : Fin stages.length) (s : State) (a : Action) : ℝ :=
  (stateAfter (stages.take i.val) ρ).expectation (fun x ↦
    (trajectoryLaw [stages.get i] x).expectation (fun path ↦
      if x = s ∧ path.1 = a then 1 else 0))

/-- State occupancy is the actual final-state event in the trajectory law for
the stages preceding the requested decision. -/
theorem stateOccupancy_eq_trajectory_event
    (stages : List (DecisionStage State Action)) (ρ : FiniteDistribution State)
    (i : Fin stages.length) (s : State) :
    stateOccupancy stages ρ i s =
      ρ.expectation (fun x ↦ (trajectoryLaw (stages.take i.val) x).expectation
        (fun path ↦ if finalState (stages.take i.val).length x path = s then 1 else 0)) := by
  classical
  calc
    stateOccupancy stages ρ i s =
        (stateAfter (stages.take i.val) ρ).expectation (fun x ↦ if x = s then 1 else 0) := by
          simp [stateOccupancy, FiniteDistribution.expectation]
    _ = _ := stateAfter_expectation_eq_trajectory _ _ _

/-- The joint event samples the actual preceding trajectory and then the
current stage's trajectory, rather than assuming the product formula. -/
theorem stateActionOccupancy_eq_trajectory_event
    (stages : List (DecisionStage State Action)) (ρ : FiniteDistribution State)
    (i : Fin stages.length) (s : State) (a : Action) :
    stateActionOccupancy stages ρ i s a =
      ρ.expectation (fun x ↦ (trajectoryLaw (stages.take i.val) x).expectation
        (fun path ↦
          (trajectoryLaw [stages.get i] (finalState (stages.take i.val).length x path)).expectation
            (fun next ↦ if finalState (stages.take i.val).length x path = s ∧
              next.1 = a then 1 else 0))) := by
  exact stateAfter_expectation_eq_trajectory _ _ _

/-- The first state law is the initial distribution, when a first stage exists. -/
@[simp] theorem stateOccupancy_first (stage : DecisionStage State Action)
    (tail : List (DecisionStage State Action)) (ρ : FiniteDistribution State) (s : State) :
    stateOccupancy (stage :: tail) ρ ⟨0, by simp⟩ s = ρ.prob s := by
  simp [stateOccupancy, stateAfter]

/-- Marginalizing the generated action and transition path yields the policy
probability of the requested action, provided the initial state is the target. -/
private theorem oneStep_event (stage : DecisionStage State Action) (x s : State)
    (a : Action) :
    (trajectoryLaw [stage] x).expectation (fun path ↦
      if x = s ∧ path.1 = a then 1 else 0) =
      if x = s then (stage.policy x).prob a else 0 := by
  classical
  rw [trajectoryExpectation_cons]
  by_cases h : x = s
  · subst x
    simp [FiniteDistribution.expectation, FiniteDistribution.sum_prob]
  · simp [h, FiniteDistribution.expectation]

/-- The joint event is the product of the state occupancy and the corresponding
nonstationary policy probability, for every actual decision time. -/
theorem stateActionOccupancy_eq (stages : List (DecisionStage State Action))
    (ρ : FiniteDistribution State) (i : Fin stages.length) (s : State) (a : Action) :
    stateActionOccupancy stages ρ i s a =
      stateOccupancy stages ρ i s * ((stages.get i).policy s).prob a := by
  classical
  unfold stateActionOccupancy
  simp_rw [oneStep_event]
  simp [stateOccupancy, FiniteDistribution.expectation]

end StatisticalRL.DecisionStage

import Formalization.MDP.ActionTrajectoryDefinitions
import Formalization.MDP.FiniteTrajectory
import Mathlib.Data.List.TakeDrop

/-!
# Action-conditioned finite trajectory return and indexed Bellman equations

The first action is fixed, the next state is sampled from its actual transition
kernel, and every later action is sampled from the policy at the visited state.
The action-conditioned return is an actual finite expectation of cumulative
path reward, not a definition by the desired Bellman equation.

Source: Chapter 2, Section 2.2 of arXiv:2610.41903v1,
`defn:Q-pi-finite`, `eq:defn-V-pi-finite`, and `eq:Bellman-finite-pi`.
-/

open scoped BigOperators

namespace StatisticalRL.DecisionStage

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Arbitrary path payoffs condition by a finite sum over the next state. -/
theorem actionTrajectoryExpectation (stage : DecisionStage State Action)
    (tail : List (DecisionStage State Action)) (s : State) (a : Action)
    (f : State × FinitePath State Action tail.length → ℝ) :
    (actionTrajectoryLaw stage tail s a).expectation f =
      (stage.transition s a).expectation (fun t ↦
        (trajectoryLaw tail t).expectation (fun path ↦ f (t, path))) := by
  simp only [FiniteDistribution.expectation, actionTrajectoryLaw, trajectoryLaw,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- The full path law is the mixture of the laws with the first action fixed. -/
theorem pathWeight_cons_actionTrajectoryLaw (stage : DecisionStage State Action)
    (tail : List (DecisionStage State Action)) (s : State) (a : Action)
    (path : State × FinitePath State Action tail.length) :
    pathWeight (stage :: tail) s (a, path) =
      (stage.policy s).prob a * (actionTrajectoryLaw stage tail s a).prob path := by
  exact mul_assoc _ _ _

@[simp]
theorem trajectoryQ_nil (s : State) (a : Action) :
    trajectoryQ ([] : List (DecisionStage State Action)) s a = 0 := rfl

/-- First-step Bellman decomposition derived from the action-conditioned law. -/
theorem trajectoryQ_cons (stage : DecisionStage State Action)
    (tail : List (DecisionStage State Action)) (s : State) (a : Action) :
    trajectoryQ (stage :: tail) s a = stage.qBackup (trajectoryValue tail) s a := by
  change (actionTrajectoryLaw stage tail s a).expectation (fun path ↦
    stage.reward s a + pathReward tail path.1 path.2) = _
  rw [actionTrajectoryExpectation]
  simp_rw [FiniteDistribution.expectation_add, FiniteDistribution.expectation_const]
  rfl

/-- Sampling the first action recovers the original state-conditioned value. -/
theorem trajectoryValue_eq_policy_expectation_Q (stage : DecisionStage State Action)
    (tail : List (DecisionStage State Action)) (s : State) :
    trajectoryValue (stage :: tail) s =
      (stage.policy s).expectation (trajectoryQ (stage :: tail) s) := by
  have hQ : trajectoryQ (stage :: tail) s = stage.qBackup (trajectoryValue tail) s := by
    funext a
    exact trajectoryQ_cons stage tail s a
  rw [trajectoryValue_cons, hQ]
  rfl

/-- Time-indexed trajectory value, including its terminal time. Index `i`
corresponds to the source's time `h = i + 1`; `i = H` is terminal. -/
def trajectoryValueAt (stages : List (DecisionStage State Action))
    (i : Fin (stages.length + 1)) : State → ℝ :=
  trajectoryValue (stages.drop i.val)

/-- The action-conditioned trajectory return at any valid or terminal time. -/
def trajectoryQAt (stages : List (DecisionStage State Action))
    (i : Fin (stages.length + 1)) : State → Action → ℝ :=
  trajectoryQ (stages.drop i.val)

@[simp]
theorem trajectoryValueAt_zero (stages : List (DecisionStage State Action)) (s : State) :
    trajectoryValueAt stages 0 s = trajectoryValue stages s := by
  simp only [trajectoryValueAt, Fin.val_zero, List.drop_zero]

@[simp]
theorem trajectoryQAt_zero (stages : List (DecisionStage State Action))
    (s : State) (a : Action) : trajectoryQAt stages 0 s a = trajectoryQ stages s a := by
  simp only [trajectoryQAt, Fin.val_zero, List.drop_zero]

/-- The source's `V_{H+1} = 0` convention at the actual terminal suffix. -/
@[simp]
theorem trajectoryValueAt_terminal (stages : List (DecisionStage State Action)) (s : State) :
    trajectoryValueAt stages (Fin.last stages.length) s = 0 := by
  simp only [trajectoryValueAt, Fin.val_last, List.drop_length, trajectoryValue_nil]

/-- The source's `Q_{H+1} = 0` convention at the actual terminal suffix. -/
@[simp]
theorem trajectoryQAt_terminal (stages : List (DecisionStage State Action))
    (s : State) (a : Action) : trajectoryQAt stages (Fin.last stages.length) s a = 0 := by
  simp only [trajectoryQAt, Fin.val_last, List.drop_length, trajectoryQ_nil]

/-- The action-value Bellman equation at every nonterminal source time.
`i.castSucc` is the current time and `i.succ` its next time. -/
theorem trajectoryQAt_bellman (stages : List (DecisionStage State Action))
    (i : Fin stages.length) (s : State) (a : Action) :
    trajectoryQAt stages i.castSucc s a =
      (stages.get i).reward s a +
        ((stages.get i).transition s a).expectation (trajectoryValueAt stages i.succ) := by
  change trajectoryQ (stages.drop i.val) s a =
    (stages.get i).reward s a + ((stages.get i).transition s a).expectation
      (trajectoryValue (stages.drop (i.val + 1)))
  rw [List.drop_eq_getElem_cons i.isLt, trajectoryQ_cons]
  rfl

/-- The state-value Bellman equation at every nonterminal source time. -/
theorem trajectoryValueAt_bellman (stages : List (DecisionStage State Action))
    (i : Fin stages.length) (s : State) :
    trajectoryValueAt stages i.castSucc s =
      ((stages.get i).policy s).expectation (trajectoryQAt stages i.castSucc s) := by
  change trajectoryValue (stages.drop i.val) s =
    ((stages.get i).policy s).expectation (trajectoryQ (stages.drop i.val) s)
  rw [List.drop_eq_getElem_cons i.isLt]
  exact trajectoryValue_eq_policy_expectation_Q _ _ s

/-- The two policy Bellman relations together, with their shared stage and
continuation value. This applies to all valid states/actions and all `h ≤ H`. -/
theorem trajectory_bellman_at (stages : List (DecisionStage State Action))
    (i : Fin stages.length) (s : State) (a : Action) :
    (trajectoryQAt stages i.castSucc s a =
      (stages.get i).reward s a +
        ((stages.get i).transition s a).expectation (trajectoryValueAt stages i.succ)) ∧
    (trajectoryValueAt stages i.castSucc s =
      ((stages.get i).policy s).expectation (trajectoryQAt stages i.castSucc s)) :=
  ⟨trajectoryQAt_bellman stages i s a, trajectoryValueAt_bellman stages i s⟩

/-- The indexed trajectory value agrees with backward evaluation of the
corresponding actual suffix, including the terminal index. -/
theorem trajectoryValueAt_eq_backwardValue (stages : List (DecisionStage State Action))
    (i : Fin (stages.length + 1)) (s : State) :
    trajectoryValueAt stages i s = backwardValue (stages.drop i.val) s :=
  trajectoryValue_eq_backwardValue _ _

end StatisticalRL.DecisionStage

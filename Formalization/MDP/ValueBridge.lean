import Formalization.OfflineRL.LCBQDefinitions
import Formalization.Generative.PolicyLearningAbsorbingPreservation
import Formalization.ModelFree.QLearningOptimalFluctuation
import Formalization.Federated.LowerBound.InnerConstantRefutation
import Formalization.MDP.ControlledEnvironmentDefinitions
import Formalization.MDP.DiscountedFiniteTrajectory
import Formalization.MDP.PolicyValueQ
import Formalization.MDP.FixedPoint

/-!
# Bridges between the library's value-function notions

This module is purely additive: it states and proves relations between existing definitions and
changes none of them.

## Optimal value `V⋆` of a discounted MDP

The library carries four spellings of the optimal value of a `DiscountedMDP`:

* `OfflineRL.LCBQ.optValue`,
* `ModelBasedPolicyLearning.optimalTrajectoryValue`,
* `QLearning.qTrueOptimalValue`,

all of which are *by definition* `M.trajectoryExpectedValue M.optimalGreedyPolicy`, the actual
infinite-trajectory value of the greedy policy of the Bellman-optimality fixed point
(`optValue_eq_optimalTrajectoryValue`, `optimalTrajectoryValue_eq_qTrueOptimalValue`, both `rfl`
and valid for every discounted MDP); and
* `Ch7Rest.FedGeneric.vStar`, defined as `max_a Q⋆(·, a)` through an `iSup`.  It agrees with the
  three above for every MDP (`vStar_eq_optimalTrajectoryValue`); here the `iSup` is the genuine
  maximum because the action type is finite and nonempty.  The equality uses the library lemma
  `optimalTrajectoryValue_eq_actionMaximum`, not a hypothesis on the data.

All four are also `actionMaximum (M.optimalityFixedPoint s)` (`optValue_eq_actionMaximum`).

Not identified with these, on purpose: the finite-horizon `EnvironmentStage.optimalValue` /
`optimalQ` and `backwardValue` (a different model, a list of nonstationary stages with zero
terminal value, no discounting) are values of a horizon-`H` problem.  They are not equal to the
discounted `V⋆` of a stationary MDP in general (for example at horizon `0` they vanish while
`V⋆ ≥ 0` need not), so no equality is stated.

## Fixed points

`valueFixedPoint`, `policyFixedPoint` and `optimalityFixedPoint` are selected with
`Classical.choose` from an `∃!`; here they are identified with Mathlib's
`ContractingWith.fixedPoint` of the corresponding Bellman operator.

## Stage backups

`DecisionStage.qBackup` and `EnvironmentStage.qBackup` agree once a policy is attached with
`EnvironmentStage.withPolicy`.
-/

namespace StatisticalRL

section OptimalValue

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The offline-RL `optValue` is the model-based `optimalTrajectoryValue`. -/
theorem optValue_eq_optimalTrajectoryValue (M : DiscountedMDP State Action) :
    OfflineRL.LCBQ.optValue M = ModelBasedPolicyLearning.optimalTrajectoryValue M := rfl

/-- The model-based `optimalTrajectoryValue` is the Q-learning `qTrueOptimalValue`. -/
theorem optimalTrajectoryValue_eq_qTrueOptimalValue (M : DiscountedMDP State Action) :
    ModelBasedPolicyLearning.optimalTrajectoryValue M = QLearning.qTrueOptimalValue M := rfl

/-- The offline-RL `optValue` is the Q-learning `qTrueOptimalValue`. -/
theorem optValue_eq_qTrueOptimalValue (M : DiscountedMDP State Action) :
    OfflineRL.LCBQ.optValue M = QLearning.qTrueOptimalValue M := rfl

/-- The optimal value is the maximum of the optimal action-value fixed point. -/
theorem optValue_eq_actionMaximum (M : DiscountedMDP State Action) (s : State) :
    OfflineRL.LCBQ.optValue M s =
      letI : Nonempty Action := M.action_nonempty
      actionMaximum (M.optimalityFixedPoint s) :=
  ModelBasedPolicyLearning.optimalTrajectoryValue_eq_actionMaximum M s

end OptimalValue

section VStar

variable {State Action : Type} [Fintype State] [Fintype Action]
  [Nonempty State] [Nonempty Action]

omit [Nonempty State] in
/-- The federated `vStar` (`max_a Q⋆(·,a)` as an `iSup`) is the optimal trajectory value. -/
theorem vStar_eq_optimalTrajectoryValue (M : DiscountedMDP State Action) :
    Ch7Rest.FedGeneric.vStar M = ModelBasedPolicyLearning.optimalTrajectoryValue M := by
  funext s
  rw [ModelBasedPolicyLearning.optimalTrajectoryValue_eq_actionMaximum]
  simp only [Ch7Rest.FedGeneric.vStar, Ch7Rest.Fed.greedyValue, actionMaximum,
    Finset.sup'_univ_eq_ciSup]

omit [Nonempty State] in
/-- The federated `vStar` is the offline-RL `optValue`. -/
theorem vStar_eq_optValue (M : DiscountedMDP State Action) :
    Ch7Rest.FedGeneric.vStar M = OfflineRL.LCBQ.optValue M :=
  vStar_eq_optimalTrajectoryValue M

end VStar

section FixedPoints

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The selected state-value fixed point is Mathlib's `ContractingWith.fixedPoint`. -/
theorem valueFixedPoint_eq_contractingFixedPoint (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) [Nonempty State] :
    M.valueFixedPoint π =
      ContractingWith.fixedPoint (M.valueBellman π) (M.valueBellman_contracting π) :=
  ((M.valueFixedPoint_characterization π _).mp
    (ContractingWith.fixedPoint_isFixedPt (f := M.valueBellman π)
      (hf := M.valueBellman_contracting π))).symm

/-- The selected action-value fixed point of a policy is Mathlib's
`ContractingWith.fixedPoint`. -/
theorem policyFixedPoint_eq_contractingFixedPoint (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) [Nonempty State] [Nonempty Action] :
    M.policyFixedPoint π =
      ContractingWith.fixedPoint (M.qBellman π) (M.qBellman_contracting π) :=
  ((M.policyFixedPoint_characterization π _).mp
    (ContractingWith.fixedPoint_isFixedPt (f := M.qBellman π)
      (hf := M.qBellman_contracting π))).symm

/-- The selected optimality fixed point is Mathlib's `ContractingWith.fixedPoint`. -/
theorem optimalityFixedPoint_eq_contractingFixedPoint (M : DiscountedMDP State Action)
    [Nonempty State] [Nonempty Action] :
    M.optimalityFixedPoint =
      ContractingWith.fixedPoint M.qOptimality M.qOptimality_contracting :=
  ((M.optimalityFixedPoint_characterization _).mp
    (ContractingWith.fixedPoint_isFixedPt (f := M.qOptimality)
      (hf := M.qOptimality_contracting))).symm

end FixedPoints

section StageBackups

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Attaching a policy does not change the action-value backup. -/
theorem DecisionStage.qBackup_withPolicy (e : EnvironmentStage State Action)
    (π : StationaryPolicy State Action) (V : State → ℝ) :
    (e.withPolicy π).qBackup V = e.qBackup V := rfl

/-- The decision-stage value backup of an attached policy averages the environment's
`qBackup` over the policy. -/
theorem DecisionStage.valueBackup_withPolicy (e : EnvironmentStage State Action)
    (π : StationaryPolicy State Action) (V : State → ℝ) (s : State) :
    (e.withPolicy π).valueBackup V s = (π s).expectation (e.qBackup V s) := rfl

/-- The backup of the stage induced by a stationary discounted MDP is the undiscounted
one-step reward plus expected continuation. -/
theorem DecisionStage.qBackup_stationaryStage (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V : State → ℝ) (s : State) (a : Action) :
    (M.stationaryStage π).qBackup V s a = M.reward s a + (M.transition s a).expectation V := rfl

end StageBackups

end StatisticalRL

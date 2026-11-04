import Formalization.Generative.FiniteHorizonPolicyEvaluationConsumption

import Formalization.Statements.Ch3Definitions
/-! Actual all-stage V and forced-action Q performance for the concrete causal
selector, retaining the safe all-level confidence/log factor. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance performanceConsumptionStateMeasurable : MeasurableSpace State := ⊤

theorem policyTrajectorySuffix_le_optimal (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (h : ℕ) (s : State) :
    policyTrajectorySuffix es f h s ≤ EnvironmentStage.optimalValue (es.drop h) s := by
  rw [policyTrajectorySuffix, EnvironmentStage.controlled_drop]
  exact EnvironmentStage.trajectoryValue_le_optimal _ _ _

theorem backwardGreedyActions_policyTrajectorySuffix (fallback : Action)
    (es : List (EnvironmentStage State Action)) (h : ℕ) :
    policyTrajectorySuffix es (backwardGreedyActions fallback es) h =
      EnvironmentStage.optimalValue (es.drop h) := by
  funext s
  rw [policyTrajectorySuffix, EnvironmentStage.controlled_drop]
  have hf : (fun k ↦ deterministicPolicy (backwardGreedyActions fallback es) (h + k)) =
      deterministicPolicy (backwardGreedyActions fallback (es.drop h)) := by
    funext k t
    exact congrArg EnvironmentStage.pointMass (backwardGreedyActions_drop fallback es h k t)
  rw [hf, controlled_backwardGreedyActions]
  exact EnvironmentStage.greedy_trajectoryValue _ _

/-- Uniform future value loss controls the genuine forced-first-action Q loss. -/
theorem policyTrajectoryQSuffix_loss_le_of_values
    (es : List (EnvironmentStage State Action)) (f : ℕ → State → Action) (C : ℝ)
    (hC : 0 ≤ C)
    (hV : ∀ h s, EnvironmentStage.optimalValue (es.drop h) s - policyTrajectorySuffix es f h s ≤ C)
    (h : ℕ) (s : State) (a : Action) :
    0 ≤ EnvironmentStage.optimalQ (es.drop h) s a - policyTrajectoryQSuffix es f h s a ∧
      EnvironmentStage.optimalQ (es.drop h) s a - policyTrajectoryQSuffix es f h s a ≤ C := by
  constructor
  · apply sub_nonneg.mpr
    rw [policyTrajectoryQSuffix, EnvironmentStage.controlled_drop]
    exact EnvironmentStage.trajectoryQ_le_optimal _ _ _ _
  · cases hd : es.drop h with
    | nil => simp [policyTrajectoryQSuffix, EnvironmentStage.controlled_drop, hd,
        EnvironmentStage.optimalQ, EnvironmentStage.controlled, DecisionStage.trajectoryQ_nil, hC]
    | cons E tail =>
      have ht : es.drop (h + 1) = tail := by
        simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero, Nat.add_comm] using
          congrArg (List.drop 1) hd
      have hv (t : State) : EnvironmentStage.optimalValue tail t -
          DecisionStage.trajectoryValue (EnvironmentStage.controlled tail
            (fun k ↦ deterministicPolicy f (h + (k + 1)))) t ≤ C := by
        have hh := hV (h + 1) t
        rw [policyTrajectorySuffix, EnvironmentStage.controlled_drop, ht] at hh
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      have he : EnvironmentStage.optimalQ (es.drop h) s a - policyTrajectoryQSuffix es f h s a =
          (E.transition s a).expectation (fun t ↦ EnvironmentStage.optimalValue tail t -
            DecisionStage.trajectoryValue (EnvironmentStage.controlled tail
              (fun k ↦ deterministicPolicy f (h + (k + 1)))) t) := by
        simp only [policyTrajectoryQSuffix, EnvironmentStage.controlled_drop, hd,
          EnvironmentStage.optimalQ, EnvironmentStage.controlled, DecisionStage.trajectoryQ_cons,
          DecisionStage.qBackup, EnvironmentStage.qBackup, EnvironmentStage.withPolicy,
          FiniteDistribution.expectation_sub]
        ring
      rw [hd] at he
      rw [he]
      exact (E.transition s a).expectation_le_const hv

/-- The two actual evaluation errors imply all-stage V and Q loss for the
same concrete empirical backward planner, on the same common event. -/
theorem allLevelBernsteinEvent_policyPerformance {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (hH : 0 < H) (fallback : Action)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 12 * (H : ℝ) * allLevelBeta (H := H) State Action δ < N)
    (data : Samples State Action H N)
    (hevent : AllLevelBernsteinEvent E N hN fallback
      (backwardGreedyActions fallback (List.ofFn E)) δ data) :
    let f := backwardGreedyActions fallback (empiricalStages E N hN data)
    ∀ h : ℕ,
      (∀ s, 0 ≤ EnvironmentStage.optimalValue ((List.ofFn E).drop h) s -
          policyTrajectorySuffix (List.ofFn E) f h s ∧
        EnvironmentStage.optimalValue ((List.ofFn E).drop h) s -
          policyTrajectorySuffix (List.ofFn E) f h s ≤
          12 * H * Real.sqrt (3 * allLevelBeta (H := H) State Action δ * H / (N : ℝ))) ∧
      (∀ s a, 0 ≤ EnvironmentStage.optimalQ ((List.ofFn E).drop h) s a -
          policyTrajectoryQSuffix (List.ofFn E) f h s a ∧
        EnvironmentStage.optimalQ ((List.ofFn E).drop h) s a -
          policyTrajectoryQSuffix (List.ofFn E) f h s a ≤
          12 * H * Real.sqrt (3 * allLevelBeta (H := H) State Action δ * H / (N : ℝ))) := by
  let f := backwardGreedyActions fallback (empiricalStages E N hN data)
  let fixed := backwardGreedyActions fallback (List.ofFn E)
  let r : ℝ := 6 * H * Real.sqrt (3 * allLevelBeta (H := H) State Action δ * H / (N : ℝ))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hv (h : ℕ) (s : State) :
      0 ≤ EnvironmentStage.optimalValue ((List.ofFn E).drop h) s - policyTrajectorySuffix (List.ofFn E) f h s ∧
      EnvironmentStage.optimalValue ((List.ofFn E).drop h) s - policyTrajectorySuffix (List.ofFn E) f h s ≤ 2 * r := by
    have htrue := allLevelBernsteinEvent_policyEvaluation E N hN hH fallback fixed δ hδ hδ1 hsize data hevent true h
    have hfit := allLevelBernsteinEvent_policyEvaluation E N hN hH fallback fixed δ hδ hδ1 hsize data hevent false h
    change ‖policyTrajectorySuffix (empiricalStages E N hN data) fixed h -
      policyTrajectorySuffix (List.ofFn E) fixed h‖ ≤ r at htrue
    change ‖policyTrajectorySuffix (empiricalStages E N hN data) f h -
      policyTrajectorySuffix (List.ofFn E) f h‖ ≤ r at hfit
    have ht := (norm_le_pi_norm (policyTrajectorySuffix (empiricalStages E N hN data) fixed h -
      policyTrajectorySuffix (List.ofFn E) fixed h) s).trans htrue
    have hf := (norm_le_pi_norm (policyTrajectorySuffix (empiricalStages E N hN data) f h -
      policyTrajectorySuffix (List.ofFn E) f h) s).trans hfit
    simp only [Pi.sub_apply, Real.norm_eq_abs] at ht hf
    have hop := policyTrajectorySuffix_le_optimal (empiricalStages E N hN data) fixed h s
    have htrueeq := congrFun (backwardGreedyActions_policyTrajectorySuffix fallback (List.ofFn E) h) s
    have hfiteq := congrFun (backwardGreedyActions_policyTrajectorySuffix fallback (empiricalStages E N hN data) h) s
    refine ⟨sub_nonneg.mpr (policyTrajectorySuffix_le_optimal _ f h s), ?_⟩
    have htl := (abs_le.mp ht).1
    have hfl := (abs_le.mp hf).2
    change policyTrajectorySuffix (List.ofFn E) fixed h s = _ at htrueeq
    change policyTrajectorySuffix (empiricalStages E N hN data) f h s = _ at hfiteq
    linarith
  dsimp only
  intro h
  constructor
  · intro s
    have hh := hv h s
    refine ⟨hh.1, ?_⟩
    calc
      _ ≤ 2 * r := hh.2
      _ = _ := by dsimp [r]; ring
  · intro s a
    have hh := policyTrajectoryQSuffix_loss_le_of_values (List.ofFn E) f (2 * r)
      (mul_nonneg (by norm_num) hr) (fun h s ↦ (hv h s).2) h s a
    refine ⟨hh.1, ?_⟩
    calc
      _ ≤ 2 * r := hh.2
      _ = _ := by dsimp [r]; ring

/-- The actual causal algorithm enjoys both all-stage performance bounds on a
single probability event, with the explicit unabsorbed confidence logarithm. -/
theorem causalPolicyPerformance_probability {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (hH : 0 < H) (fallback : Action)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 12 * (H : ℝ) * allLevelBeta (H := H) State Action δ < N) :
    1 - δ < (samplingLaw E N).real {data | CausalPolicyPerformanceEvent E N hN fallback
      (12 * H * Real.sqrt (3 * allLevelBeta (H := H) State Action δ * H / (N : ℝ))) data} := by
  have hp := allLevelBernsteinEvent_probability E N hN hH fallback
    (backwardGreedyActions fallback (List.ofFn E)) δ hδ hδ1
  apply hp.trans_le
  apply measureReal_mono _ (measure_ne_top (samplingLaw E N) _)
  intro data hd
  exact allLevelBernsteinEvent_policyPerformance E N hN hH fallback δ hδ hδ1 hsize data hd

end StatisticalRL.FiniteHorizonGenerative

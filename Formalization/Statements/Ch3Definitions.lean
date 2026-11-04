import Formalization.Probability.EmpiricalRow
import Formalization.MDP.DiscountedFiniteTrajectory
import Formalization.MDP.InfiniteReturn
import Formalization.MDP.ForcedActionReturn
import Formalization.MDP.OptimalTrajectoryValue
import Formalization.MDP.FiniteOptimal
import Formalization.MDP.FiniteQTrajectory
import Mathlib.Data.List.OfFn
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! Chapter 3 source-facing objects. This module contains definitions only. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyEvaluation
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance ch3EvalStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance ch3EvalStateDecidable : DecidableEq State := Classical.decEq State

/-- The sample at index `(s,i)` is the `i`th draw from the policy row at `s`. -/
abbrev Samples (State : Type*) (N : ℕ) := (State × Fin N) → State

/-- The actual product experiment of policy-induced transition rows. -/
noncomputable def samplingLaw (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) : Measure (Samples State N) :=
  Measure.pi (fun i : State × Fin N ↦ (M.policyTransition π i.1).rowMeasure)

/-- The empirical policy transition row consists of observed frequencies. -/
noncomputable def empiricalPolicyRow (N : ℕ) (hN : 0 < N)
    (data : Samples State N) (s : State) : FiniteDistribution State :=
  FiniteDistribution.empiricalRow N hN (fun i ↦ data (s, i))

/-- Embed the empirical policy kernel and the known policy reward in an MDP.
Its action rows are identical, so its policy value is the plug-in value. -/
noncomputable def empiricalModel (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) : DiscountedMDP State Action where
  state_nonempty := M.state_nonempty
  action_nonempty := M.action_nonempty
  transition := fun s _ ↦ empiricalPolicyRow N hN data s
  reward := fun s _ ↦ (π s).expectation (M.reward s)
  reward_nonneg := by
    intro s a
    exact (π s).expectation_nonneg (M.reward_nonneg s)
  reward_le_one := by
    intro s a
    exact (π s).expectation_le_const (M.reward_le_one s)
  discount := M.discount
  discount_nonneg := M.discount_nonneg
  discount_lt_one := M.discount_lt_one

/-- The unique discounted Bellman solution on the empirical policy model. -/
noncomputable def valueEstimator (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) : State → ℝ :=
  (empiricalModel M π N hN data).valueFixedPoint π
end StatisticalRL.ModelBasedPolicyEvaluation

namespace StatisticalRL.ModelBasedPolicyLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance ch3EvalStateMeasurable : MeasurableSpace State := ⊤
local instance ch3LearnActionMeasurable : MeasurableSpace Action := ⊤
noncomputable local instance ch3EvalStateDecidable : DecidableEq State := Classical.decEq State

/-- One observation for each state-action pair and sample index. -/
abbrev Samples (State Action : Type*) (N : ℕ) := ((State × Action) × Fin N) → State

/-- The genuine product of the true state-action transition row laws. -/
noncomputable def samplingLaw (M : DiscountedMDP State Action) (N : ℕ) :
    Measure (Samples State Action N) :=
  Measure.pi (fun i : (State × Action) × Fin N ↦ (M.transition i.1.1 i.1.2).rowMeasure)

/-- The empirical row is the frequency vector of that state-action's draws. -/
noncomputable def empiricalRow (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (s : State) (a : Action) : FiniteDistribution State :=
  FiniteDistribution.empiricalRow N hN (fun i ↦ data ((s, a), i))

/-- The sample model has the empirical kernel and the original known reward and discount. -/
noncomputable def empiricalModel (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) : DiscountedMDP State Action where
  state_nonempty := M.state_nonempty
  action_nonempty := M.action_nonempty
  transition := empiricalRow N hN data
  reward := M.reward
  reward_nonneg := M.reward_nonneg
  reward_le_one := M.reward_le_one
  discount := M.discount
  discount_nonneg := M.discount_nonneg
  discount_lt_one := M.discount_lt_one

/-- The empirical optimal Q-function obtained from the optimal Bellman fixed point. -/
noncomputable def qEstimator (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) : State → Action → ℝ :=
  (empiricalModel M N hN data).optimalityFixedPoint

/-- A deterministic greedy empirical-optimal action, including a choice for ties. -/
noncomputable def policyEstimator (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) : State → Action :=
  (empiricalModel M N hN data).optimalGreedyAction

/-- The empirical optimal value is the actual trajectory value of the output policy. -/
noncomputable def valueEstimator (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) : State → ℝ :=
  (empiricalModel M N hN data).trajectoryExpectedValue
    (fun s ↦ EnvironmentStage.pointMass (policyEstimator M N hN data s))
end StatisticalRL.ModelBasedPolicyLearning

namespace StatisticalRL.ModelBasedPolicyLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Actual empirical trajectory optimality, against all stationary policies. -/
def EmpiricallyOptimal (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (f : State → Action) : Prop :=
  ∀ π s, (empiricalModel M N hN data).trajectoryExpectedValue π s ≤
    (empiricalModel M N hN data).trajectoryExpectedValue
      (fun t ↦ EnvironmentStage.pointMass (f t)) s
end StatisticalRL.ModelBasedPolicyLearning

namespace StatisticalRL.ModelBasedPolicyLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance ch3AbsorbingStateDecidable : DecidableEq State := Classical.decEq State

/-- Replace every transition at x by absorption and every reward there by
`(1−γ)u`, leaving all other rows unchanged. -/
noncomputable def stateAbsorbingModel (M : DiscountedMDP State Action)
    (x : State) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / (1 - M.discount)) :
    DiscountedMDP State Action where
  state_nonempty := M.state_nonempty
  action_nonempty := M.action_nonempty
  transition := fun s a ↦ if s = x then EnvironmentStage.pointMass x else M.transition s a
  reward := fun s a ↦ if s = x then (1 - M.discount) * u else M.reward s a
  reward_nonneg := by
    intro s a
    split
    · exact mul_nonneg (sub_pos.mpr M.discount_lt_one).le hu0
    · exact M.reward_nonneg s a
  reward_le_one := by
    intro s a
    split
    · have h := (le_div_iff₀ (sub_pos.mpr M.discount_lt_one)).mp hu1
      nlinarith
    · exact M.reward_le_one s a
  discount := M.discount
  discount_nonneg := M.discount_nonneg
  discount_lt_one := M.discount_lt_one
end StatisticalRL.ModelBasedPolicyLearning

namespace StatisticalRL.ModelBasedPolicyLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance ch3PreservationStateDecidable : DecidableEq State := Classical.decEq State

/-- The source's value V* as an actual optimal-policy trajectory value. -/
noncomputable def optimalTrajectoryValue (M : DiscountedMDP State Action) : State → ℝ :=
  M.trajectoryExpectedValue M.optimalGreedyPolicy

/-- Absorb at x with u equal to the original model's actual optimal value at x. -/
noncomputable def optimalValueAbsorbingModel (M : DiscountedMDP State Action) (x : State) :
    DiscountedMDP State Action :=
  stateAbsorbingModel M x (optimalTrajectoryValue M x)
    (M.trajectoryExpectedValue_bounds M.optimalGreedyPolicy x).1
    (M.trajectoryExpectedValue_bounds M.optimalGreedyPolicy x).2
end StatisticalRL.ModelBasedPolicyLearning

namespace StatisticalRL.ModelBasedPolicyLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance ch3GridRealDecidable : DecidableEq ℝ := Classical.decEq ℝ
noncomputable local instance ch3GridValueDecidable : DecidableEq (State → ℝ) := Classical.decEq _

noncomputable def absorbingGridStep (M : DiscountedMDP State Action) (N : ℕ) (_hN : 0 < N) : ℝ :=
  1 / ((N : ℝ) * (1 - M.discount))

noncomputable def absorbingGridPoint (M : DiscountedMDP State Action) (N : ℕ) (_hN : 0 < N)
    (i : Fin (N + 1)) : ℝ := (i : ℝ) / ((N : ℝ) * (1 - M.discount))

noncomputable def absorbingGridValue (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (x : State) (i : Fin (N + 1)) : State → ℝ := by
  let u := absorbingGridPoint M N hN i
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hgap : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hD : 0 < (N : ℝ) * (1 - M.discount) := mul_pos hNreal hgap
  have hi : (i : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hu0 : 0 ≤ u := by
    dsimp [u, absorbingGridPoint]
    exact div_nonneg (by positivity) hD.le
  have hu1 : u ≤ 1 / (1 - M.discount) := by
    dsimp [u, absorbingGridPoint]
    apply (div_le_iff₀ hD).2
    have heq : (1 / (1 - M.discount)) *
        ((N : ℝ) * (1 - M.discount)) = N := by field_simp
    rw [heq]
    exact hi
  exact optimalTrajectoryValue (stateAbsorbingModel M x u hu0 hu1)
end StatisticalRL.ModelBasedPolicyLearning

namespace StatisticalRL.ModelBasedPolicyLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance ch3AllRowStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance ch3AllRowStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance ch3AllRowActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The source's policy-learning logarithmic parameter. -/
noncomputable def leaveOneOutBeta (M : DiscountedMDP State Action) (N : ℕ) (δ : ℝ) : ℝ :=
  2 * Real.log (16 * Fintype.card State * Fintype.card Action * N /
    ((1 - M.discount) * δ))
end StatisticalRL.ModelBasedPolicyLearning

namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance ch3FiniteStageStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance ch3FiniteStageStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance ch3FiniteStageActionDecidable : DecidableEq Action := Classical.decEq Action

abbrev SampleIndex (State Action : Type*) (H N : ℕ) := (Fin H × State × Action) × Fin N

abbrev Samples (State Action : Type*) (H N : ℕ) := SampleIndex State Action H N → State

/-- N actual independent next-state observations at every stage/state/action. -/
noncomputable def samplingLaw {H : ℕ} (E : Fin H → EnvironmentStage State Action) (N : ℕ) :
    Measure (Samples State Action H N) :=
  Measure.pi (fun i : SampleIndex State Action H N ↦
    ((E i.1.1).transition i.1.2.1 i.1.2.2).rowMeasure)

/-- The empirical stage keeps the original known reward exactly. -/
noncomputable def empiricalStage {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action H N) (h : Fin H) :
    EnvironmentStage State Action where
  state_nonempty := (E h).state_nonempty
  action_nonempty := (E h).action_nonempty
  transition := fun s a ↦ FiniteDistribution.empiricalRow N hN (fun i ↦ data ((h,s,a),i))
  reward := (E h).reward
  reward_nonneg := (E h).reward_nonneg
  reward_le_one := (E h).reward_le_one
end StatisticalRL.FiniteHorizonGenerative

namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance ch3FiniteContinuationStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance ch3FiniteContinuationStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance ch3FiniteContinuationActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The actual empirical environment stages in chronological order. -/
noncomputable def empiricalStages {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action H N) :
    List (EnvironmentStage State Action) := List.ofFn (empiricalStage E N hN data)
end StatisticalRL.FiniteHorizonGenerative

namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance ch3AuxiliaryVarianceStateMeasurable : MeasurableSpace State := ⊤

/-- The same fixed deterministic nonstationary policy in both models. -/
noncomputable def deterministicPolicy (f : ℕ → State → Action) : ℕ → StationaryPolicy State Action :=
  fun k s ↦ EnvironmentStage.pointMass (f k s)
end StatisticalRL.FiniteHorizonGenerative

namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance ch3FittedAuxiliaryStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance ch3FittedAuxiliaryStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance ch3FittedAuxiliaryActionDecidable : DecidableEq Action := Classical.decEq Action

/-- A deterministic local greedy selector; fallback only acts after the episode. -/
noncomputable def backwardGreedyActions (fallback : Action) :
    List (EnvironmentStage State Action) → ℕ → State → Action
  | [], _ => fun _ ↦ fallback
  | E :: es, 0 => E.greedyAction (EnvironmentStage.optimalValue es)
  | _ :: es, n + 1 => backwardGreedyActions fallback es n
end StatisticalRL.FiniteHorizonGenerative

namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance ch3EvaluationConsumptionStateMeasurable : MeasurableSpace State := ⊤

/-- Actual expected cumulative trajectory reward from an episode suffix. -/
noncomputable def policyTrajectorySuffix (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (h : ℕ) : State → ℝ :=
  DecisionStage.trajectoryValue ((EnvironmentStage.controlled es (deterministicPolicy f)).drop h)

/-- The source's forced-first-action trajectory Q on the same suffix. -/
noncomputable def policyTrajectoryQSuffix (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (h : ℕ) : State → Action → ℝ :=
  DecisionStage.trajectoryQ ((EnvironmentStage.controlled es (deterministicPolicy f)).drop h)
end StatisticalRL.FiniteHorizonGenerative

namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance ch3PerformanceConsumptionStateMeasurable : MeasurableSpace State := ⊤

/-- Simultaneous actual V/Q performance of the specified causal planner. -/
def CausalPolicyPerformanceEvent {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (R : ℝ) (data : Samples State Action H N) : Prop :=
    let f := backwardGreedyActions fallback (empiricalStages E N hN data)
    ∀ h : ℕ,
      (∀ s, 0 ≤ EnvironmentStage.optimalValue ((List.ofFn E).drop h) s -
          policyTrajectorySuffix (List.ofFn E) f h s ∧
        EnvironmentStage.optimalValue ((List.ofFn E).drop h) s -
          policyTrajectorySuffix (List.ofFn E) f h s ≤ R) ∧
      (∀ s a, 0 ≤ EnvironmentStage.optimalQ ((List.ofFn E).drop h) s a -
          policyTrajectoryQSuffix (List.ofFn E) f h s a ∧
        EnvironmentStage.optimalQ ((List.ofFn E).drop h) s a -
          policyTrajectoryQSuffix (List.ofFn E) f h s a ≤ R)
end StatisticalRL.FiniteHorizonGenerative

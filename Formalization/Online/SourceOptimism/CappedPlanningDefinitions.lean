import Formalization.MDP.EnvironmentDefinitions
import Formalization.MDP.OptimalityOperatorDefinitions
import Formalization.Probability.FiniteSampleDefinitions
import Formalization.Probability.VarianceDefinitions
import Formalization.Online.SourceOptimism.ZeroCountUpdateDefinitions
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
/-- A known-reward stage and its observed successor lists, before one episode.
The environment carries the source reward bounds and nonempty finite carriers. -/
structure OnlineObservedPlanningStage (State Action : Type*)
    [Fintype State] [Fintype Action] where
  environment : EnvironmentStage State Action
  observations : State → Action → List State

/-- Uniform initialization of an unvisited row, as in the source algorithm. -/
noncomputable def onlineUniformInitialRow [Nonempty State] : FiniteDistribution State where
  prob _ := (Fintype.card State : ℝ)⁻¹
  prob_nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_prob := by
    have hcard : (Fintype.card State : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

/-- Observed frequency row at positive count; source uniform initialization at
zero. Positive count uses the existing actual empirical-frequency definition. -/
noncomputable def onlineObservedPlanningRow
    (stage : OnlineObservedPlanningStage State Action) (s : State) (a : Action) :
    FiniteDistribution State := by
  letI : Nonempty State := stage.environment.state_nonempty
  let xs := stage.observations s a
  exact if h : 0 < xs.length then
    FiniteDistribution.empiricalRow xs.length h (fun i => xs.get i)
  else onlineUniformInitialRow

/-- One capped backup with known reward, the same observed row for mean and
variance, and the explicit unvisited-row correction. -/
noncomputable def onlineCappedStageQ
    (cap L c₁ c₂ : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (next : State → ℝ) (s : State) (a : Action) : ℝ :=
  onlineZeroCountSafeQUpdate (stage.environment.reward s a)
    ((onlineObservedPlanningRow stage s a).expectation next)
    ((onlineObservedPlanningRow stage s a).variance next)
    cap L c₁ c₂ (stage.observations s a).length

/-- Backward value recursion. The cap stays equal to the global horizon,
including at late stages, and the terminal continuation is exactly zero. -/
noncomputable def onlineCappedBackwardValue (cap L c₁ c₂ : ℝ) :
    List (OnlineObservedPlanningStage State Action) → State → ℝ
  | [] => fun _ => 0
  | stage :: stages => fun s =>
    letI : Nonempty Action := stage.environment.action_nonempty
    actionMaximum (onlineCappedStageQ cap L c₁ c₂ stage
      (onlineCappedBackwardValue cap L c₁ c₂ stages) s)

/-- The Q table shares exactly the continuation used by the value recursion. -/
noncomputable def onlineCappedBackwardQ (cap L c₁ c₂ : ℝ) :
    List (OnlineObservedPlanningStage State Action) → State → Action → ℝ
  | [] => fun _ _ => 0
  | stage :: stages => onlineCappedStageQ cap L c₁ c₂ stage
      (onlineCappedBackwardValue cap L c₁ c₂ stages)

/-- Stage-indexed full table, with zero values after the supplied horizon. -/
noncomputable def onlineCappedBackwardValueAt (cap L c₁ c₂ : ℝ)
    (stages : List (OnlineObservedPlanningStage State Action)) (h : ℕ) : State → ℝ :=
  onlineCappedBackwardValue cap L c₁ c₂ (stages.drop h)

noncomputable def onlineCappedBackwardQAt (cap L c₁ c₂ : ℝ)
    (stages : List (OnlineObservedPlanningStage State Action)) (h : ℕ) :
    State → Action → ℝ :=
  onlineCappedBackwardQ cap L c₁ c₂ (stages.drop h)


end StatisticalRL.OnlineRL

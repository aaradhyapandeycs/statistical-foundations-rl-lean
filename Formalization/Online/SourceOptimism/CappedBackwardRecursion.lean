import Formalization.MDP.FiniteOptimal
import Formalization.Probability.EmpiricalRow
import Formalization.Probability.Variance
import Formalization.Online.OnlineZeroCountOptimisticUpdate

/-!
Construction for onlineRL.tex Algorithm UCBVI.
A stage carries its actual known-reward environment and chronological observed
successors for every row. No independence, concentration or optimism is assumed.
Zero observed count explicitly leaves Q at H; every positive-count backup is the
printed capped update. The map from actual online histories to these lists and
the identification of the deployed planner remain separate proof obligations.
-/
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

/-- Exact positive-count row, with its actual list-indexed observations. -/
theorem onlineObservedPlanningRow_positive
    (stage : OnlineObservedPlanningStage State Action) (s : State) (a : Action)
    (h : 0 < (stage.observations s a).length) :
    onlineObservedPlanningRow stage s a =
      FiniteDistribution.empiricalRow (stage.observations s a).length h
        (fun i => (stage.observations s a).get i) := by
  simp [onlineObservedPlanningRow, h]

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

/-- Deterministic range of one backup; the variance need not be bounded to prove
this range because its real square root is nonnegative and the update is capped. -/
theorem onlineCappedStageQ_range
    (cap L c₁ c₂ : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (next : State → ℝ) (hnext : ∀ s, 0 ≤ next s)
    (hcap : 0 ≤ cap) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (s : State) (a : Action) :
    0 ≤ onlineCappedStageQ cap L c₁ c₂ stage next s a ∧
      onlineCappedStageQ cap L c₁ c₂ stage next s a ≤ cap := by
  exact onlineZeroCountSafeQUpdate_range _ _ _ _ _ _ _ _
    (stage.environment.reward_nonneg s a)
    ((onlineObservedPlanningRow stage s a).expectation_nonneg hnext)
    hcap hL hc₁ hc₂

/-- Unvisited rows retain the global optimistic cap, without a zero denominator. -/
theorem onlineCappedStageQ_zero_count
    (cap L c₁ c₂ : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (next : State → ℝ) (s : State) (a : Action)
    (hzero : (stage.observations s a).length = 0) :
    onlineCappedStageQ cap L c₁ c₂ stage next s a = cap := by
  simp [onlineCappedStageQ, hzero, onlineZeroCountSafeQUpdate_zero]

/-- Every positive-count row has exactly the printed source backup. -/
theorem onlineCappedStageQ_positive_count
    (cap L c₁ c₂ : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (next : State → ℝ) (s : State) (a : Action)
    (hpos : 0 < (stage.observations s a).length) :
    onlineCappedStageQ cap L c₁ c₂ stage next s a =
      min (stage.environment.reward s a +
        (onlineObservedPlanningRow stage s a).expectation next +
        c₁ * Real.sqrt ((onlineObservedPlanningRow stage s a).variance next * L /
          (stage.observations s a).length) +
        c₂ * cap * L / (stage.observations s a).length) cap := by
  exact onlineZeroCountSafeQUpdate_positive _ _ _ _ _ _ _ _ hpos

/-- Deterministic value range for every supplied observed data list, without any
sampling or concentration assumptions. -/
theorem onlineCappedBackwardValue_range
    (cap L c₁ c₂ : ℝ) (hcap : 0 ≤ cap) (hL : 0 ≤ L)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (stages : List (OnlineObservedPlanningStage State Action)) :
    ∀ s, 0 ≤ onlineCappedBackwardValue cap L c₁ c₂ stages s ∧
      onlineCappedBackwardValue cap L c₁ c₂ stages s ≤ cap := by
  induction stages with
  | nil => intro s; exact ⟨le_rfl, hcap⟩
  | cons stage stages ih =>
    intro s
    letI : Nonempty Action := stage.environment.action_nonempty
    let q := onlineCappedStageQ cap L c₁ c₂ stage
      (onlineCappedBackwardValue cap L c₁ c₂ stages) s
    have hq (a : Action) : 0 ≤ q a ∧ q a ≤ cap :=
      onlineCappedStageQ_range cap L c₁ c₂ stage _ (fun x => (ih x).1)
        hcap hL hc₁ hc₂ s a
    obtain ⟨a, ha⟩ := EnvironmentStage.exists_maximizer q
    change 0 ≤ actionMaximum q ∧ actionMaximum q ≤ cap
    rw [← ha]
    exact hq a

/-- The shared Q table has the same deterministic range at all suffixes. -/
theorem onlineCappedBackwardQ_range
    (cap L c₁ c₂ : ℝ) (hcap : 0 ≤ cap) (hL : 0 ≤ L)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (stages : List (OnlineObservedPlanningStage State Action)) (s : State) (a : Action) :
    0 ≤ onlineCappedBackwardQ cap L c₁ c₂ stages s a ∧
      onlineCappedBackwardQ cap L c₁ c₂ stages s a ≤ cap := by
  cases stages with
  | nil => exact ⟨le_rfl, hcap⟩
  | cons stage stages =>
    exact onlineCappedStageQ_range cap L c₁ c₂ stage _
      (fun x => (onlineCappedBackwardValue_range cap L c₁ c₂ hcap hL hc₁ hc₂ stages x).1)
      hcap hL hc₁ hc₂ s a

/-- Both stage-indexed tables are deterministically in the source interval. -/
theorem onlineCappedBackwardAt_range
    (cap L c₁ c₂ : ℝ) (hcap : 0 ≤ cap) (hL : 0 ≤ L)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (stages : List (OnlineObservedPlanningStage State Action)) (h : ℕ) :
    (∀ s, 0 ≤ onlineCappedBackwardValueAt cap L c₁ c₂ stages h s ∧
      onlineCappedBackwardValueAt cap L c₁ c₂ stages h s ≤ cap) ∧
    (∀ s a, 0 ≤ onlineCappedBackwardQAt cap L c₁ c₂ stages h s a ∧
      onlineCappedBackwardQAt cap L c₁ c₂ stages h s a ≤ cap) := by
  exact ⟨onlineCappedBackwardValue_range cap L c₁ c₂ hcap hL hc₁ hc₂ _,
    onlineCappedBackwardQ_range cap L c₁ c₂ hcap hL hc₁ hc₂ _⟩

end StatisticalRL.OnlineRL

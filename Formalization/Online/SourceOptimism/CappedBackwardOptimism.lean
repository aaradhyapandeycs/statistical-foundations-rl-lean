import Formalization.Online.SourceOptimism.CappedBackupCertificate

/-! Chronological backward optimism induction.
Source active stage h is suffix drop(h−1); terminal V is zero. The empty Q
extension is not an additional source stage. Actual history certificates and
trajectory-value identification are separate adapters, not assumed here. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The true environments stay in the chronological order of observed stages. -/
def onlinePlanningEnvironments (stages : List (OnlineObservedPlanningStage State Action)) :
    List (EnvironmentStage State Action) := stages.map (fun stage => stage.environment)

/-- Actual finite-horizon Bellman optimum range, derived solely from true
reward bounds and stochastic rows. Its trajectory characterization is already
provided by EnvironmentStage.greedy_trajectoryValue and greedy_trajectoryQ. -/
theorem onlineTrueOptimalValue_range_length
    (es : List (EnvironmentStage State Action)) :
    ∀ s, 0 ≤ EnvironmentStage.optimalValue es s ∧
      EnvironmentStage.optimalValue es s ≤ (es.length : ℝ) := by
  induction es with
  | nil => intro s; simp [EnvironmentStage.optimalValue]
  | cons e es ih =>
    intro s
    letI : Nonempty Action := e.action_nonempty
    obtain ⟨a, ha⟩ := EnvironmentStage.exists_maximizer
      (e.qBackup (EnvironmentStage.optimalValue es) s)
    change 0 ≤ actionMaximum (e.qBackup (EnvironmentStage.optimalValue es) s) ∧
      actionMaximum (e.qBackup (EnvironmentStage.optimalValue es) s) ≤ _
    rw [← ha]
    have hlo := (e.transition s a).expectation_nonneg (fun x => (ih x).1)
    have hhi := (e.transition s a).expectation_le_const (fun x => (ih x).2)
    have hrlo := e.reward_nonneg s a
    have hrhi := e.reward_le_one s a
    simp only [EnvironmentStage.qBackup, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> linarith

/-- Certificate at each chronological suffix, uniform in the later optimistic
continuation. No inequality about the current Q/V output occurs in this input. -/
def onlineChronologicalBonusCertificates (cap L c₁ c₂ : ℝ) :
    List (OnlineObservedPlanningStage State Action) → Prop
  | [] => True
  | stage :: stages =>
    (∀ s a, 3 ≤ (stage.observations s a).length →
      ∀ U : State → ℝ,
      (∀ x, EnvironmentStage.optimalValue (onlinePlanningEnvironments stages) x ≤ U x ∧
        U x ≤ cap) →
      (stage.environment.transition s a).expectation
          (EnvironmentStage.optimalValue (onlinePlanningEnvironments stages)) ≤
        (onlineObservedPlanningRow stage s a).expectation U +
          c₁ * Real.sqrt ((onlineObservedPlanningRow stage s a).variance U *
            (L / (stage.observations s a).length)) +
          c₂ * cap * (L / (stage.observations s a).length)) ∧
    onlineChronologicalBonusCertificates cap L c₁ c₂ stages

/-- Backward induction derives both optimal Bellman Q and V lower bounds from
row certificates on the same observed lists. The cap is at least the global
number of stages. Its source instantiation sets cap=H exactly. -/
theorem onlineCappedBackward_dominates_trueOptimal
    (cap L c₁ c₂ : ℝ) (hcap : 0 ≤ cap) (hL : 1 ≤ L)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (stages : List (OnlineObservedPlanningStage State Action))
    (hlen : (stages.length : ℝ) ≤ cap)
    (hcertificate : onlineChronologicalBonusCertificates cap L c₁ c₂ stages) :
    (∀ s, EnvironmentStage.optimalValue (onlinePlanningEnvironments stages) s ≤
      onlineCappedBackwardValue cap L c₁ c₂ stages s) ∧
    (∀ s a, EnvironmentStage.optimalQ (onlinePlanningEnvironments stages) s a ≤
      onlineCappedBackwardQ cap L c₁ c₂ stages s a) := by
  revert hlen hcertificate
  induction stages with
  | nil =>
    intro _ _
    exact ⟨fun _ => le_rfl, fun _ _ => le_rfl⟩
  | cons stage stages ih =>
    intro hlen hcertificate
    have hlenTail : (stages.length : ℝ) ≤ cap := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hlen
      linarith
    have htail := ih hlenTail hcertificate.2
    have htruthRange := onlineTrueOptimalValue_range_length
      (onlinePlanningEnvironments stages)
    have htruthUpper (x : State) :
        EnvironmentStage.optimalValue (onlinePlanningEnvironments stages) x ≤ cap - 1 := by
      have hx := (htruthRange x).2
      simp only [onlinePlanningEnvironments, List.length_map] at hx
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hlen
      have htailcap : (stages.length : ℝ) ≤ cap - 1 := by linarith
      exact hx.trans htailcap
    have hc₁nonneg : 0 ≤ c₁ := by linarith
    have hc₂nonneg : 0 ≤ c₂ := (sq_nonneg c₁).trans hc₂
    have hnextRange := onlineCappedBackwardValue_range cap L c₁ c₂ hcap
      (by linarith) hc₁nonneg hc₂nonneg stages
    have hQ (s : State) (a : Action) :
        stage.environment.qBackup
            (EnvironmentStage.optimalValue (onlinePlanningEnvironments stages)) s a ≤
          onlineCappedStageQ cap L c₁ c₂ stage
            (onlineCappedBackwardValue cap L c₁ c₂ stages) s a :=
      onlineCappedStageQ_ge_trueBackup_all_counts cap L c₁ c₂ stage _ _ s a
        hcap hL hc₁ hc₂ (fun x => (htruthRange x).1) htruthUpper
        (fun x => ⟨htail.1 x, (hnextRange x).2⟩) (hcertificate.1 s a)
    constructor
    · intro s
      letI : Nonempty Action := stage.environment.action_nonempty
      obtain ⟨a, ha⟩ := EnvironmentStage.exists_maximizer
        (stage.environment.qBackup
          (EnvironmentStage.optimalValue (onlinePlanningEnvironments stages)) s)
      change actionMaximum (stage.environment.qBackup
          (EnvironmentStage.optimalValue (onlinePlanningEnvironments stages)) s) ≤
        actionMaximum (onlineCappedStageQ cap L c₁ c₂ stage
          (onlineCappedBackwardValue cap L c₁ c₂ stages) s)
      rw [← ha]
      exact (hQ s a).trans (le_actionMaximum _ a)
    · exact hQ

end StatisticalRL.OnlineRL

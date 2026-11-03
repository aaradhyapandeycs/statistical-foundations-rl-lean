import Formalization.Online.SourceOptimism.CappedBackwardRecursion

/-! Deterministic one-stage consumption of a row
certificate. No output optimism is a premise: the true Bellman backup cap is
derived from reward≤1 and a bound on the true next-stage continuation. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The actual known-reward Bellman backup is below the global cap if the true
continuation has at most cap−1 remaining reward. This is a proved input for
capping, not an assumed inequality about the optimistic output. -/
theorem onlineTrueBackup_le_cap
    (cap : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (truth : State → ℝ) (htruth : ∀ x, truth x ≤ cap - 1)
    (s : State) (a : Action) :
    stage.environment.qBackup truth s a ≤ cap := by
  have hmean := (stage.environment.transition s a).expectation_le_const htruth
  have hr := stage.environment.reward_le_one s a
  dsimp [EnvironmentStage.qBackup]
  linarith

/-- At a large observed count, a transition-mean certificate for this same
computed continuation implies the capped Q backup dominates the true Bellman
backup. The source's certificate variance convention is preserved. -/
theorem onlineCappedStageQ_ge_trueBackup_of_certificate
    (cap L c₁ c₂ : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (truth next : State → ℝ) (s : State) (a : Action)
    (hpos : 0 < (stage.observations s a).length)
    (htruth : ∀ x, truth x ≤ cap - 1)
    (hcertificate : (stage.environment.transition s a).expectation truth ≤
      (onlineObservedPlanningRow stage s a).expectation next +
        c₁ * Real.sqrt ((onlineObservedPlanningRow stage s a).variance next *
          (L / (stage.observations s a).length)) +
        c₂ * cap * (L / (stage.observations s a).length)) :
    stage.environment.qBackup truth s a ≤
      onlineCappedStageQ cap L c₁ c₂ stage next s a := by
  rw [onlineCappedStageQ_positive_count cap L c₁ c₂ stage next s a hpos]
  apply le_min
  · have hc : (stage.environment.transition s a).expectation truth ≤
        (onlineObservedPlanningRow stage s a).expectation next +
          c₁ * Real.sqrt ((onlineObservedPlanningRow stage s a).variance next * L /
            (stage.observations s a).length) +
          c₂ * cap * L / (stage.observations s a).length := by
      simpa only [mul_div_assoc] using hcertificate
    dsimp [EnvironmentStage.qBackup]
    linarith
  · exact onlineTrueBackup_le_cap cap stage truth htruth s a

/-- All observed counts are handled: zero/one/two are deterministic saturation;
larger counts consume a uniform continuation certificate. The next continuation
is allowed to be data-dependent; the certificate is universal before selection.
The truth/range relations are precisely the next-stage induction inputs, not
an assumption of the desired current-stage conclusion. -/
theorem onlineCappedStageQ_ge_trueBackup_all_counts
    (cap L c₁ c₂ : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (truth next : State → ℝ) (s : State) (a : Action)
    (hcap : 0 ≤ cap) (hL : 1 ≤ L) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (htruthNonneg : ∀ x, 0 ≤ truth x)
    (htruth : ∀ x, truth x ≤ cap - 1)
    (hnext : ∀ x, truth x ≤ next x ∧ next x ≤ cap)
    (hcertificate : 3 ≤ (stage.observations s a).length →
      ∀ U : State → ℝ, (∀ x, truth x ≤ U x ∧ U x ≤ cap) →
        (stage.environment.transition s a).expectation truth ≤
          (onlineObservedPlanningRow stage s a).expectation U +
            c₁ * Real.sqrt ((onlineObservedPlanningRow stage s a).variance U *
              (L / (stage.observations s a).length)) +
            c₂ * cap * (L / (stage.observations s a).length)) :
    stage.environment.qBackup truth s a ≤
      onlineCappedStageQ cap L c₁ c₂ stage next s a := by
  by_cases hsmall : (stage.observations s a).length ≤ 2
  · have hc₁nonneg : 0 ≤ c₁ := by linarith
    have hc₂two : 2 ≤ c₂ := by nlinarith [sq_nonneg (c₁ - 4)]
    have hmean : 0 ≤ (onlineObservedPlanningRow stage s a).expectation next :=
      (onlineObservedPlanningRow stage s a).expectation_nonneg
        (fun x => (htruthNonneg x).trans (hnext x).1)
    have hsat : onlineCappedStageQ cap L c₁ c₂ stage next s a = cap :=
      onlineZeroCountSafeQUpdate_small _ _ _ _ _ _ _ _ hsmall
        (stage.environment.reward_nonneg s a) hmean hcap hL hc₁nonneg hc₂two
    rw [hsat]
    exact onlineTrueBackup_le_cap cap stage truth htruth s a
  · have hlarge : 3 ≤ (stage.observations s a).length := by omega
    exact onlineCappedStageQ_ge_trueBackup_of_certificate cap L c₁ c₂ stage
      truth next s a (by omega) htruth (hcertificate hlarge next hnext)

end StatisticalRL.OnlineRL

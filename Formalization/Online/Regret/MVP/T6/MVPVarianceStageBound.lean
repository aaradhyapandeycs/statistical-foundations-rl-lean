import Formalization.Online.Regret.T5.OnlineT5Scalar

/-! Uncompiled one-stage deterministic ingredient for `lem:bound-T6-ucb-mvp`.
It is generic in the planning stage; the actual MVP played-action maximizer
and completed-history stage identity must be supplied by the pathwise consumer. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action] [Nonempty Action]

theorem mvp_greedy_trueMean_square_bound
    (cap L c₁ c₂ : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (tail : List (OnlineObservedPlanningStage State Action)) (s : State) (a : Action)
    (hcap : 0 ≤ cap) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hgreedy : onlineCappedStageQ cap L c₁ c₂ stage
      (onlineCappedBackwardValue cap L c₁ c₂ tail) s a =
      actionMaximum (onlineCappedStageQ cap L c₁ c₂ stage
        (onlineCappedBackwardValue cap L c₁ c₂ tail) s)) :
    let V := onlineCappedBackwardValue cap L c₁ c₂ (stage :: tail) s
    let U := onlineCappedBackwardValue cap L c₁ c₂ tail
    let P := (stage.environment.transition s a).expectation U
    let Phat := (onlineObservedPlanningRow stage s a).expectation U
    V^2 - P^2 ≤ 2*cap*(stage.environment.reward s a +
      onlineRegretAnalysisCharge cap L c₁ c₂ stage U s a + max (Phat-P) 0) := by
  classical
  let U := onlineCappedBackwardValue cap L c₁ c₂ tail
  let P := (stage.environment.transition s a).expectation U
  let Phat := (onlineObservedPlanningRow stage s a).expectation U
  have hV := onlineCappedBackwardValue_range cap L c₁ c₂ hcap hL hc₁ hc₂ (stage :: tail) s
  have hU := onlineCappedBackwardValue_range cap L c₁ c₂ hcap hL hc₁ hc₂ tail
  have hP0 : 0 ≤ P := (stage.environment.transition s a).expectation_nonneg (fun x => (hU x).1)
  have hPH : P ≤ cap := (stage.environment.transition s a).expectation_le_const (fun x => (hU x).2)
  have hcharge := onlineRegretAnalysisCharge_nonneg_for_T5 cap L c₁ c₂ stage U s a hcap hL hc₁ hc₂
  have hbackup := onlineCappedStageQ_le_analysisBackup cap L c₁ c₂ stage U (fun x => (hU x).1) s a
  have hvalue : onlineCappedBackwardValue cap L c₁ c₂ (stage :: tail) s =
      onlineCappedStageQ cap L c₁ c₂ stage U s a := by
    change actionMaximum (onlineCappedStageQ cap L c₁ c₂ stage U s) = _
    exact hgreedy.symm
  have hr := stage.environment.reward_nonneg s a
  have hb : 0 ≤ stage.environment.reward s a +
      onlineRegretAnalysisCharge cap L c₁ c₂ stage U s a + max (Phat-P) 0 := by
    positivity
  apply onlineT5_square_sub_le_backup cap _ P _ hcap hV.1 hV.2 hP0 hPH hb
  rw [hvalue]
  have hmax : Phat-P ≤ max (Phat-P) 0 := le_max_left _ _
  dsimp [P, Phat] at hmax ⊢
  linarith
end StatisticalRL.OnlineRL

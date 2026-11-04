import Formalization.Online.Regret.Telescope

/-! Actual-law variance and gap proof component: OnlineT5Scalar.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL

/-- A capped greedy value controlled by the empirical mean plus a nonnegative
reward-and-charge increment has the source square-difference bound. -/
theorem onlineT5_square_sub_le_backup (H x y b : ℝ)
    (hH : 0 ≤ H) (hx0 : 0 ≤ x) (hxH : x ≤ H)
    (hy0 : 0 ≤ y) (hyH : y ≤ H) (hb : 0 ≤ b)
    (hbackup : x ≤ y + b) :
    x^2 - y^2 ≤ 2 * H * b := by
  by_cases hxy : x ≤ y
  · have hh : 0 ≤ 2 * H * b := by positivity
    nlinarith
  · have hsum : 0 ≤ 2 * H - (x + y) := by linarith
    have hdiff : 0 ≤ x - y := by linarith
    have hproduct := mul_nonneg hsum hdiff
    have hrest := mul_nonneg (show 0 ≤ 2 * H by positivity) (show 0 ≤ b - (x - y) by linarith)
    nlinarith
end StatisticalRL.OnlineRL

namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem onlineRegretAnalysisCharge_nonneg_for_T5
    (cap L c₁ c₂ : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (next : State → ℝ) (s : State) (a : Action)
    (hcap : 0 ≤ cap) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    0 ≤ onlineRegretAnalysisCharge cap L c₁ c₂ stage next s a := by
  unfold onlineRegretAnalysisCharge
  split_ifs with hpos
  · positivity
  · exact hcap

/-- The source square estimate for one greedy stage, including a zero-count
row through the already-proved corrected analysis-backup theorem. -/
theorem onlineT5_greedy_stage_square_bound
    [Nonempty Action] (cap L c₁ c₂ : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (tail : List (OnlineObservedPlanningStage State Action)) (s : State) (a : Action)
    (hcap : 0 ≤ cap) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hgreedy : onlineCappedStageQ cap L c₁ c₂ stage
      (onlineCappedBackwardValue cap L c₁ c₂ tail) s a =
      actionMaximum (onlineCappedStageQ cap L c₁ c₂ stage
        (onlineCappedBackwardValue cap L c₁ c₂ tail) s)) :
    let V := onlineCappedBackwardValue cap L c₁ c₂ (stage :: tail) s
    let U := onlineCappedBackwardValue cap L c₁ c₂ tail
    let m := (onlineObservedPlanningRow stage s a).expectation U
    V^2 - m^2 ≤ 2 * cap *
      (stage.environment.reward s a + onlineRegretAnalysisCharge cap L c₁ c₂ stage U s a) := by
  classical
  let U := onlineCappedBackwardValue cap L c₁ c₂ tail
  let m := (onlineObservedPlanningRow stage s a).expectation U
  have hV := onlineCappedBackwardValue_range cap L c₁ c₂ hcap hL hc₁ hc₂ (stage :: tail) s
  have hU := onlineCappedBackwardValue_range cap L c₁ c₂ hcap hL hc₁ hc₂ tail
  have hm0 : 0 ≤ m := (onlineObservedPlanningRow stage s a).expectation_nonneg (fun x => (hU x).1)
  have hmH : m ≤ cap := (onlineObservedPlanningRow stage s a).expectation_le_const (fun x => (hU x).2)
  have hcharge := onlineRegretAnalysisCharge_nonneg_for_T5 cap L c₁ c₂ stage U s a hcap hL hc₁ hc₂
  have hbackup := onlineCappedStageQ_le_analysisBackup cap L c₁ c₂ stage U (fun x => (hU x).1) s a
  have hvalue : onlineCappedBackwardValue cap L c₁ c₂ (stage :: tail) s =
      onlineCappedStageQ cap L c₁ c₂ stage U s a := by
    change actionMaximum (onlineCappedStageQ cap L c₁ c₂ stage U s) = _
    exact hgreedy.symm
  apply onlineT5_square_sub_le_backup cap _ m _ hcap hV.1 hV.2 hm0 hmH
    (add_nonneg (stage.environment.reward_nonneg s a) hcharge)
  rw [hvalue]
  dsimp [m]
  linarith
end StatisticalRL.OnlineRL

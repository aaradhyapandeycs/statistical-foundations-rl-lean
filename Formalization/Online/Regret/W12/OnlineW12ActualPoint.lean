import Formalization.Online.Regret.W12.OnlineW12AbsolutePointwise
import Formalization.Online.Regret.W1.OnlineW1ActualRadiusAlignment
import Formalization.Online.Regret.W2.OnlineW2ActualBudget

/-! Same-experiment suffix proof component: OnlineW12ActualPoint.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w12PointState : DecidableEq State := Classical.decEq State
noncomputable local instance w12PointAction : DecidableEq Action := Classical.decEq Action

noncomputable def onlineActualW1Point
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) : ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let V := onlineTrueSuffixRowFamily E (h, sa)
  (onlineObservedPlanningRow stage sa.1 sa.2).expectation V - ((E h).transition sa.1 sa.2).expectation V

theorem onlineActualW1Point_abs_le_radius
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ)
    (hcert : onlineObservedTrueW1Certificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path))
    (h : Fin H) (k : Fin K) :
    |onlineActualW1Point H K hH E initial fallback path δ c₁ c₂ h k| ≤
      onlineActualW1RadiusTerm H K hH E initial fallback path δ c₁ c₂ h k := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  have hb := onlineObservedW1_pointwise_abs_bound H K E history k h sa.1 sa.2 δ hcert
  simpa [onlineActualW1Point, onlineActualW1RadiusTerm, onlineActualW1Count, planner, history, sa] using hb

theorem onlineActualW2Point_abs_le_radius
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hcert : onlineObservedW2CoordinateCertificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path))
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path))
    (h : Fin H) (k : Fin K) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let n := onlineActualW1Count H K hH E initial fallback path δ c₁ c₂ h k
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
    let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
    let d := ((E h).transition sa.1 sa.2).expectation (fun s => (U s - P s)^2)
    |onlineActualW2Point H K hH E initial fallback path δ c₁ c₂ h k| ≤
      if 3 ≤ n then Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) * d / n) +
        (Fintype.card State : ℝ) * H * Real.log (1 / δ) / n else H := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let n := onlineActualW1Count H K hH E initial fallback path δ c₁ c₂ h k
  let gap := onlineActualW2Gap H K hH E initial fallback path δ c₁ c₂ h k
  have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ).2 (by linarith))
  have hgap : ∀ s, 0 ≤ gap s ∧ gap s ≤ H := by
    intro s
    have ho := onlineActualW2_gap_order H K hH E initial fallback path δ c₁ c₂ hL hc₁ hc₂ hoptimism h k s
    dsimp [gap, onlineActualW2Gap, sa, planner] at *
    exact ⟨ho.1, le_trans ho.2.1 ho.2.2⟩
  have hp := onlineObservedW2_pointwise_abs_bound H K E history k h sa.1 sa.2 δ hδ hδsmall hcert gap hgap
  have hv := onlineActualW2_gap_variance_le_policy_difference H K hH E initial fallback path δ c₁ c₂ hL hc₁ hc₂ hoptimism h k
  change _ ≤ if 3 ≤ n then _ else _
  change _ ≤ if 3 ≤ n then _ else _ at hp
  by_cases hn : 3 ≤ n
  · simp only [if_pos hn] at hp ⊢
    have hscale : 0 ≤ 2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n := by positivity
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hv hscale)
    rw [Real.sqrt_mul hscale] at hs
    have hrewrite (d : ℝ) : Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n * d) =
        Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) * d / n) := by congr 1; ring
    rw [hrewrite] at hs
    change _ ≤ Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n) *
      Real.sqrt (((E h).transition sa.1 sa.2).variance gap) +
      (Fintype.card State : ℝ) * H * Real.log (1 / δ) / n at hp
    change Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n) *
      Real.sqrt (((E h).transition sa.1 sa.2).variance gap) ≤ _ at hs
    change |(onlineObservedPlanningRow (onlineHistoryPlanningStage E (history.take (k.val * H)) h)
      sa.1 sa.2).expectation gap - ((E h).transition sa.1 sa.2).expectation gap| ≤ _
    linarith [hp, hs]
  · simp only [if_neg hn] at hp ⊢
    exact hp
end StatisticalRL.OnlineRL

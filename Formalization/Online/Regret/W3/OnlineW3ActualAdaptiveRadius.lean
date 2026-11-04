import Formalization.Online.Regret.W3.OnlineW3AdaptivePoint
import Formalization.Online.Regret.W1.OnlineW1ActualRadiusAlignment

/-! Actual adaptive W₃ point bound using the shared W₂ coordinate event. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w3AdaptiveRadiusStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w3AdaptiveRadiusActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineActualW3AdaptivePoint_le_radius
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
    onlineActualW3AdaptivePoint H K hH E initial fallback path δ c₁ c₂ h k ≤
      if 3 ≤ n then Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) * (4 * (H : ℝ)^2 * d) / n) +
        (Fintype.card State : ℝ) * (H : ℝ)^2 * Real.log (1 / δ) / n else (H : ℝ)^2 := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let n := onlineActualW1Count H K hH E initial fallback path δ c₁ c₂ h k
  let V := onlineTrueSuffixRowFamily E (h, sa)
  let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
  let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
  let gap := fun s => (U s)^2 - (V s)^2
  have hL : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    apply (one_le_div hδ).2
    linarith
  have hg := onlineActualW3_adaptive_gap_bounds H K hH E initial fallback path δ c₁ c₂ hL hc₁ hc₂ hoptimism h k
  change (∀ s, 0 ≤ gap s ∧ gap s ≤ (H : ℝ)^2) ∧
    ((E h).transition sa.1 sa.2).variance gap ≤
      4 * (H : ℝ)^2 * ((E h).transition sa.1 sa.2).expectation (fun s => (U s - P s)^2) at hg
  have hp := onlineObservedW3_adaptive_pointwise_bound H K E history k h sa.1 sa.2 δ hδ hδsmall hcert gap hg.1
  change _ ≤ if 3 ≤ n then _ else _ at hp
  change _ ≤ if 3 ≤ n then _ else _
  by_cases hn : 3 ≤ n
  · simp only [if_pos hn] at hp ⊢
    have hscale : 0 ≤ 2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n := by positivity
    have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hg.2 hscale)
    rw [Real.sqrt_mul hscale] at hs
    have hrewrite (d : ℝ) : Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n * d) =
        Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) * d / n) := by congr 1; ring
    rw [hrewrite] at hs
    change _ ≤ Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n) *
      Real.sqrt (((E h).transition sa.1 sa.2).variance gap) +
      (Fintype.card State : ℝ) * (H : ℝ)^2 * Real.log (1 / δ) / n at hp
    change (onlineObservedPlanningRow (onlineHistoryPlanningStage E (history.take (k.val * H)) h)
      sa.1 sa.2).expectation gap - ((E h).transition sa.1 sa.2).expectation gap ≤ _
    linarith [hp, hs]
  · simp only [if_neg hn] at hp ⊢
    exact hp
end StatisticalRL.OnlineRL

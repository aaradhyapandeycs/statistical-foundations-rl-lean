import Formalization.Online.Regret.W3.OnlineW3ActualSplit

/-! The adaptive squared gap's range and variance follow from the actual
optimism event and the actual policy, without a variance premise. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w3AdaptiveStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w3AdaptiveActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineActualW3_adaptive_gap_bounds
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hL : 0 ≤ Real.log (1 / δ)) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path))
    (h : Fin H) (k : Fin K) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let V := onlineTrueSuffixRowFamily E (h, sa)
    let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
    (∀ s, 0 ≤ U s^2 - V s^2 ∧ U s^2 - V s^2 ≤ (H : ℝ)^2) ∧
    ((E h).transition sa.1 sa.2).variance (fun s => U s^2 - V s^2) ≤
      4 * (H : ℝ)^2 * ((E h).transition sa.1 sa.2).expectation (fun s => (U s - P s)^2) := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let V := onlineTrueSuffixRowFamily E (h, sa)
  let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
  let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
  have hP : ∀ s, 0 ≤ P s := by
    intro s
    dsimp [P, onlineActualPolicyContinuation]
    rw [DecisionStage.trajectoryValue_eq_backwardValue]
    exact DecisionStage.backwardValue_nonneg _ s
  have hPV : ∀ s, P s ≤ V s := by
    intro s
    have hh := onlineActualW2_gap_order H K hH E initial fallback path δ c₁ c₂ hL hc₁ hc₂ hoptimism h k s
    change 0 ≤ U s - V s ∧ U s - V s ≤ U s - P s ∧ U s - P s ≤ H at hh
    linarith [hh.2.1]
  have hVU : ∀ s, V s ≤ U s := by
    intro s
    have hh := onlineActualW2_gap_order H K hH E initial fallback path δ c₁ c₂ hL hc₁ hc₂ hoptimism h k s
    change 0 ≤ U s - V s ∧ U s - V s ≤ U s - P s ∧ U s - P s ≤ H at hh
    linarith [hh.1]
  have hUH : ∀ s, U s ≤ H := by
    intro s
    dsimp [U, onlineActualOptimisticContinuation, onlineCappedBackwardValueAt]
    exact (onlineCappedBackwardValue_range H (Real.log (1 / δ)) c₁ c₂
      (by exact_mod_cast Nat.zero_le H) hL hc₁ hc₂ _ s).2
  exact onlineW3_square_gap_bounds _ U V P H (by exact_mod_cast Nat.zero_le H) hP hPV hVU hUH
end StatisticalRL.OnlineRL

import Formalization.Online.Regret.W2.OnlineW2ActualGap

/-! Actual W₂ continuation variance is controlled by the actual squared
optimistic-to-policy gap, without a target-shaped variance hypothesis. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w2GapVarStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w2GapVarActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineActualW2_gap_variance_le_policy_difference
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hL : 0 ≤ Real.log (1 / δ)) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂))
        (K * H) [] path)) (h : Fin H) (k : Fin K) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let V := onlineTrueSuffixRowFamily E (h, sa)
    let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
    ((E h).transition sa.1 sa.2).variance (fun s => U s - V s) ≤
      ((E h).transition sa.1 sa.2).expectation (fun s => (U s - P s)^2) := by
  dsimp only
  apply (FiniteDistribution.variance_le_expectation_sq _ _).trans
  apply FiniteDistribution.expectation_mono
  intro s
  have horder := onlineActualW2_gap_order H K hH E initial fallback path δ c₁ c₂ hL hc₁ hc₂ hoptimism h k s
  dsimp only at horder
  rcases horder with ⟨hzero, hle, hcap⟩
  nlinarith [sq_nonneg ((onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k) s -
    (onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k) s -
    ((onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k) s -
      onlineTrueSuffixRowFamily E (h, (onlineActualStageRowSequence H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) path h k.val)) s))]
end StatisticalRL.OnlineRL

import Formalization.Online.Regret.Gap.OnlineJ2StageSum

/-! Actual-law variance and gap proof component: OnlineT6DifferenceActualBound.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineActualT6Difference_le_stagewiseT0_of_J1
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ T0 : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path))
    (hstage : ∀ h : Fin H,
      (∑ k : Fin K, onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ h k) ≤ T0)
    (hJ1 : |onlineActualJ1 H K hH E initial fallback path δ c₁ c₂| ≤
      Real.sqrt (8 * onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂ * Real.log (1 / δ)) +
        5 * (H : ℝ) * Real.log (1 / δ)) :
    onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂ ≤
      2 * (H : ℝ)^2 * T0 + 18 * (H : ℝ)^2 * Real.log (1 / δ) := by
  have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have hD : 0 ≤ onlineActualT6Difference H K hH E initial fallback path δ c₁ c₂ := by
    unfold onlineActualT6Difference
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.expectation_nonneg _ (fun _ => sq_nonneg _)
  have hexpand := onlineActualT6Difference_le_H_J1_add_J2 H K hH E initial fallback path δ c₁ c₂ hL hc₁ hc₂ hoptimism
  have hJ2 := onlineActualJ2_le_H_T0_of_stagewise H K hH E initial fallback path δ c₁ c₂ T0 hoptimism hstage
  apply onlineT6Difference_assemble (H : ℝ) _ _ _ T0 (Real.log (1 / δ)) (by exact_mod_cast hH) hD hL hexpand
  · exact (le_abs_self _).trans hJ1
  · exact hJ2
end StatisticalRL.OnlineRL

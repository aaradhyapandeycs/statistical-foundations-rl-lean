import Formalization.Online.Regret.Gap.OnlineJ2ActualStage

/-! Actual-law variance and gap proof component: OnlineJ2StageSum.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineActualJ2_le_stageGapSum
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path)) :
    onlineActualJ2 H K hH E initial fallback path δ c₁ c₂ ≤
      ∑ h : Fin H, ∑ k : Fin K, onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ h k := by
  classical
  let G : ℕ → ℝ := fun n => if hn : n < H then
    ∑ k : Fin K, onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ ⟨n, hn⟩ k else 0
  have hG0 : 0 ≤ G 0 := by
    simp only [G, dif_pos hH]
    exact Finset.sum_nonneg (fun k _ => onlineActualStagePolicyGap_nonneg H K hH E initial fallback path δ c₁ c₂ hoptimism ⟨0, hH⟩ k)
  have hGH : G H = 0 := by simp [G]
  have hshift : (∑ n ∈ Finset.range H, G (n + 1)) ≤ ∑ n ∈ Finset.range H, G n := by
    have h1 := Finset.sum_range_succ' G H
    have h2 := Finset.sum_range_succ G H
    linarith
  have hid : onlineActualJ2 H K hH E initial fallback path δ c₁ c₂ = ∑ n ∈ Finset.range H, G (n + 1) := by
    unfold onlineActualJ2
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro h hh
    by_cases hn : h.val + 1 < H
    · simp only [G, dif_pos hn]
      apply Finset.sum_congr rfl
      intro k hk
      exact onlineJ2_successor_gap_eq_next_stage H K hH E initial fallback path δ c₁ c₂ h k hn
    · have he : h.val + 1 = H := by omega
      simp only [G, dif_neg hn, Finset.sum_eq_zero_iff_of_nonneg]
      apply Finset.sum_eq_zero
      intro k hk
      exact onlineJ2_terminal_gap_zero H K hH E initial fallback path δ c₁ c₂ h k he _
  rw [hid]
  calc
    _ ≤ ∑ n ∈ Finset.range H, G n := hshift
    _ = _ := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro h hh
      simp [G, h.isLt]

theorem onlineActualJ2_le_H_T0_of_stagewise
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ T0 : ℝ)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path))
    (hstage : ∀ h : Fin H,
      (∑ k : Fin K, onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ h k) ≤ T0) :
    onlineActualJ2 H K hH E initial fallback path δ c₁ c₂ ≤ (H : ℝ) * T0 := by
  calc
    _ ≤ ∑ h : Fin H, ∑ k : Fin K, onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ h k :=
      onlineActualJ2_le_stageGapSum H K hH E initial fallback path δ c₁ c₂ hoptimism
    _ ≤ ∑ _h : Fin H, T0 := Finset.sum_le_sum (fun h _ => hstage h)
    _ = _ := by simp
end StatisticalRL.OnlineRL

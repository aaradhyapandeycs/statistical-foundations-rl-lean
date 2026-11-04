import Formalization.Online.Regret.T0.OnlineT0ActualSuffix
import Formalization.Online.Regret.T2.OnlineT2ActualDefinitions

/-! Same-experiment suffix proof component: OnlineT0ActualCharge.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineT0ActualSuffix_charge_nonneg
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (k : Fin K) (n : ℕ) :
    0 ≤ onlineCappedEpisodeT2 H (onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k)
      (onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k)
      (onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k) (Real.log (1 / δ)) c₁ c₂ n := by
  have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ).2 (by linarith))
  unfold onlineCappedEpisodeT2
  split_ifs
  · unfold onlineRegretAnalysisCharge
    dsimp only
    split_ifs <;> positivity
  · rfl

/-- Every episode's complete charge sum is exactly the T2 component already
used in the source actual-path decomposition. -/
theorem onlineT0ActualSuffix_charge_eq_episodeT2
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) :
    (∑ n ∈ Finset.range H,
      onlineCappedEpisodeT2 H (onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k)
        (onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k)
        (onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k) (Real.log (1 / δ)) c₁ c₂ n) =
      (onlineActualEpisodeRegretTerms H K hH E initial fallback path k δ c₁ c₂).2.1 := by
  classical
  have hs : onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k =
      (fun h => onlineHistoryPlanningStage E ((onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂))
        (K * H) [] path).take (k.val * H)) h) := by
    funext h
    rfl
  rw [hs]
  simp [onlineActualEpisodeRegretTerms, onlineT0ActualSuffixStage, onlineT0ActualSuffixState,
    onlineT0ActualSuffixAction, onlineT4EpisodeState, onlineT4PlayedAction,
    onlineCappedEpisodeT2]

/-- Nonnegative masked charges are bounded simultaneously by the full T2;
no event, independence, or count certificate is required. -/
theorem onlineT0ActualSuffix_charge_le_T2
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (j : Fin H) :
    (∑ k : Fin K, ∑ n ∈ Finset.Ico j.val H,
      onlineCappedEpisodeT2 H (onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k)
        (onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k)
        (onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k) (Real.log (1 / δ)) c₁ c₂ n) ≤
      onlineActualT2 H K hH E initial fallback path δ c₁ c₂ := by
  classical
  unfold onlineActualT2
  apply Finset.sum_le_sum
  intro k hk
  rw [← onlineT0ActualSuffix_charge_eq_episodeT2 H K hH E initial fallback path δ c₁ c₂ k]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
  · intro n hn hnot
    exact onlineT0ActualSuffix_charge_nonneg H K hH E initial fallback path δ c₁ c₂ hδ hδ1 hc₁ hc₂ k n
end StatisticalRL.OnlineRL

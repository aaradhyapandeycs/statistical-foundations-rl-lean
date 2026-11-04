import Formalization.Online.Regret.T0.OnlineT0ActualGapIdentity
import Formalization.Online.Regret.T0.OnlineT0Singleton

/-! Same-experiment suffix proof component: OnlineT0SingletonBudget.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineSingleton_actual_stageGap_le_T2 [Subsingleton State]
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{uState, 0} State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) (j : Fin H) :
    (∑ k : Fin K, onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ j k) ≤
      onlineActualT2 H K hH E initial fallback path δ c₁ c₂ := by
  classical
  have hs : (∑ k : Fin K, onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ j k) ≤
      ∑ k : Fin K, ∑ n ∈ Finset.Ico j.val H,
        onlineCappedEpisodeT2 H (onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k)
          (onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k)
          (onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k)
          (Real.log (1 / δ)) c₁ c₂ n := by
    apply Finset.sum_le_sum
    intro k hk
    have h := onlineT0ActualSuffix_gap_le_terms H K hH E initial fallback path δ c₁ c₂ hδ hδsmall hc₁ hc₂ k j
    rw [onlineActualStagePolicyGap_eq_suffix_gap]
    simpa only [onlineSingleton_suffix_T1_zero, onlineSingleton_suffix_T3_zero,
      onlineSingleton_suffix_T4_zero, Finset.sum_const_zero, zero_add, add_zero] using h
  exact hs.trans (onlineT0ActualSuffix_charge_le_T2 H K hH E initial fallback path δ c₁ c₂ hδ
    (by linarith) (by linarith) (by nlinarith [sq_nonneg c₁]) j)
end StatisticalRL.OnlineRL

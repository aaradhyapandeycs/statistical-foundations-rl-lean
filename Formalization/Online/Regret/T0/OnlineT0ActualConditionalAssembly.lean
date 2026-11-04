import Formalization.Online.Regret.T0.OnlineT0ActualGapIdentity

/-! Same-experiment suffix proof component: OnlineT0ActualConditionalAssembly.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineActualStageGap_suffix_conditional
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) (j : Fin H)
    (b₁ b₂ b₃ b₄ : ℝ)
    (hw₁ : |∑ i ∈ onlineW12SuffixIndices H K j,
      onlineActualW1Point H K hH E initial fallback path δ c₁ c₂ i.1 i.2| ≤ b₁)
    (hw₂ : |∑ i ∈ onlineW12SuffixIndices H K j,
      onlineActualW2Point H K hH E initial fallback path δ c₁ c₂ i.1 i.2| ≤ b₂)
    (hT3 : (∑ k : Fin K, ∑ n ∈ Finset.Ico j.val H,
      onlineCappedEpisodeT3 H (onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k)
        (onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k)
        (onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k)
        (Real.log (1 / δ)) c₁ c₂ n) ≤ b₃)
    (hT4 : (∑ k : Fin K,
      onlineT4SuffixEpisodeIncrement H K hH E fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) j.val k (initial, path)) ≤ b₄) :
    (∑ k : Fin K, onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ j k) ≤
      b₁ + b₂ + onlineActualT2 H K hH E initial fallback path δ c₁ c₂ + b₃ + b₄ := by
  classical
  have hs : (∑ k : Fin K, onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ j k) ≤
      ∑ k : Fin K,
        ((∑ n ∈ Finset.Ico j.val H,
          onlineCappedEpisodeT1 H (onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k)
            (onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k)
            (onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k) (Real.log (1 / δ)) c₁ c₂ n) +
        (∑ n ∈ Finset.Ico j.val H,
          onlineCappedEpisodeT2 H (onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k)
            (onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k)
            (onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k) (Real.log (1 / δ)) c₁ c₂ n) +
        (∑ n ∈ Finset.Ico j.val H,
          onlineCappedEpisodeT3 H (onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k)
            (onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k)
            (onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k) (Real.log (1 / δ)) c₁ c₂ n) +
        onlineT4SuffixEpisodeIncrement H K hH E fallback
          (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) j.val k (initial, path)) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [onlineActualStagePolicyGap_eq_suffix_gap]
    exact onlineT0ActualSuffix_gap_le_terms H K hH E initial fallback path δ c₁ c₂ hδ hδsmall hc₁ hc₂ k j
  simp only [Finset.sum_add_distrib] at hs
  rw [onlineT0ActualSuffix_T1_sum_eq_W12_masks] at hs
  have hc := onlineT0ActualSuffix_charge_le_T2 H K hH E initial fallback path δ c₁ c₂ hδ
    (by linarith) (by linarith) (by nlinarith [sq_nonneg c₁]) j
  have hw₁' := le_trans (le_abs_self _) hw₁
  have hw₂' := le_trans (le_abs_self _) hw₂
  linarith
end StatisticalRL.OnlineRL

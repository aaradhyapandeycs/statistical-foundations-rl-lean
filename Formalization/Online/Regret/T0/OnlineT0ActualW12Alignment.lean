import Formalization.Online.Regret.T0.OnlineT0ActualW12Points
/-! Same-experiment suffix proof component: OnlineT0ActualW12Alignment.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

/-- The aggregate suffix empirical error is exactly the same pair of actual
stage/episode masked sums controlled by the shared W12 suffix event. -/
theorem onlineT0ActualSuffix_T1_sum_eq_W12_masks
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (j : Fin H) :
    (∑ k : Fin K, ∑ n ∈ Finset.Ico j.val H,
      onlineCappedEpisodeT1 H (onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k)
        (onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k)
        (onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k)
        (Real.log (1 / δ)) c₁ c₂ n) =
    (∑ i ∈ onlineW12SuffixIndices H K j, onlineActualW1Point H K hH E initial fallback path δ c₁ c₂ i.1 i.2) +
    (∑ i ∈ onlineW12SuffixIndices H K j, onlineActualW2Point H K hH E initial fallback path δ c₁ c₂ i.1 i.2) := by
  classical
  have hconvert (k : Fin K) :
      (∑ n ∈ Finset.Ico j.val H,
        onlineCappedEpisodeT1 H (onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k)
          (onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k)
          (onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k)
          (Real.log (1 / δ)) c₁ c₂ n) =
      ∑ h : Fin H, if j.val ≤ h.val then
        onlineCappedEpisodeT1 H (onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k)
          (onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k)
          (onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k)
          (Real.log (1 / δ)) c₁ c₂ h.val else 0 := by
    rw [← Finset.sum_filter, onlineSumFin_suffix_eq_Ico]
    apply Finset.sum_congr rfl
    intro n hn
    simp [((Finset.mem_Ico.mp hn).2)]
  simp_rw [hconvert]
  simp only [onlineW12SuffixIndices, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hmask : j.val ≤ h.val
  · simp only [if_pos hmask]
    rw [onlineT0ActualSuffix_T1_eq_W1_add_W2]
    have halign := onlineT0ActualSuffix_W12_points H K hH E initial fallback path δ c₁ c₂ k h
    rw [halign.1, halign.2]
  · simp [hmask]
end StatisticalRL.OnlineRL

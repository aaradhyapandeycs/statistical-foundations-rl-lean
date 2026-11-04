import Formalization.Online.Regret.PolicyVariance.EpisodeVarianceClip

/-! Actual-law variance and gap proof component: OnlineEpisodeVariancePublicSum.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineActualEpisodePolicyVariance_sum_eq_T6Policy
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) :
    (∑ k : Fin K, onlineActualEpisodePolicyVariance H K hH E initial fallback path k δ c₁ c₂) =
      onlineActualT6Policy H K hH E initial fallback path δ c₁ c₂ := by
  classical
  unfold onlineActualEpisodePolicyVariance onlineActualT6Policy
  exact Finset.sum_comm

end StatisticalRL.OnlineRL

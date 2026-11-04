import Formalization.Online.Regret.PolicyVariance.OnlineEpisodeVariancePublicSum

/-! Actual-law variance and gap proof component: OnlineEpisodeVarianceRange.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineActualPolicyContinuation_range
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) (s : State) :
    0 ≤ onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k s ∧
      onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k s ≤ (H : ℝ) := by
  classical
  unfold onlineActualPolicyContinuation
  constructor
  · rw [DecisionStage.trajectoryValue_eq_backwardValue]
    exact DecisionStage.backwardValue_nonneg _ _
  · rw [DecisionStage.trajectoryValue_eq_backwardValue]
    apply (DecisionStage.backwardValue_le_length _ _).trans
    have hlen : ((EnvironmentStage.controlled (List.ofFn E)
        (onlineCappedEpisodePolicy H hH E
          (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
            (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path)
          k.val (Real.log (1 / δ)) c₁ c₂)).drop (h.val + 1)).length ≤ H := by
      rw [List.length_drop, onlineControlledStages_length, List.length_ofFn]
      exact Nat.sub_le _ _
    exact_mod_cast hlen

theorem onlineActualEpisodePolicyVariance_range
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (k : Fin K) (δ c₁ c₂ : ℝ) :
    0 ≤ onlineActualEpisodePolicyVariance H K hH E initial fallback path k δ c₁ c₂ ∧
      onlineActualEpisodePolicyVariance H K hH E initial fallback path k δ c₁ c₂ ≤ (H : ℝ)^3 := by
  classical
  unfold onlineActualEpisodePolicyVariance
  constructor
  · apply Finset.sum_nonneg
    intro h hh
    exact FiniteDistribution.variance_nonneg _ _
  · calc
      _ ≤ ∑ _h : Fin H, (H : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro h hh
        apply (FiniteDistribution.variance_le_expectation_sq _ _).trans
        apply FiniteDistribution.expectation_le_const
        intro s
        have hv := onlineActualPolicyContinuation_range H K hH E initial fallback path δ c₁ c₂ h k s
        have hHn : 0 ≤ (H : ℝ) := Nat.cast_nonneg _
        nlinarith
      _ = (H : ℝ)^3 := by simp [pow_succ]; ring
end StatisticalRL.OnlineRL

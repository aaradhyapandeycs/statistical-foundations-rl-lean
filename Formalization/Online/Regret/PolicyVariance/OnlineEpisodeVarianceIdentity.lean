import Formalization.Online.Regret.PolicyVariance.OnlineVariancePotentialActualStep
import Formalization.Online.Regret.PolicyVariance.OnlineFixedPolicyVarianceTelescope
import Formalization.Online.Regret.W1.OnlineW1ActualRowAlignment

/-! Actual-law variance and gap proof component: OnlineEpisodeVarianceIdentity.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance varianceIdentityStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance varianceIdentityActionDecidable : DecidableEq Action := Classical.decEq Action

noncomputable def onlineActualEpisodePolicyVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (k : Fin K) (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H,
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    ((E h).transition sa.1 sa.2).variance
      (onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k)

theorem onlineActualEpisodePolicyVariance_eq_potential_sub_residuals
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) (k : Fin K)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
    let stages := EnvironmentStage.controlled (List.ofFn E)
      (onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂)
    onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 k δ c₁ c₂ =
      finiteTrajectoryVariancePotential stages (sample.1 k) -
        ∑ h : Fin H, onlineVariancePotentialResidual H K hH E fallback planner k h (Real.log (1 / δ)) c₁ c₂ sample := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
  let state := onlineT4EpisodeState H K sample.1 fallback history k.val
  let g := planner (history.take (k.val * H))
  let D := onlineFixedPolicyStages E g
  let stages := EnvironmentStage.controlled (List.ofFn E)
    (onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂)
  have hD : stages = D := by
    simpa only [stages, D, g, planner, onlineT4SelectedEpisodePolicy, onlineCappedEpisodePolicy] using
      onlineT4SelectedStages_eq_fixed H hH E planner history k.val
  have hprefixlen : (history.take (k.val * H)).length = k.val * H :=
    onlineSequential_episodePrefix_length H K hH E sample.1 fallback planner sample.2 k.val k.isLt.le
  have hstate0 : state 0 = sample.1 k := by
    simpa only [state, onlineT4EpisodeState, Nat.add_zero] using
      onlineEpisodicCurrentState_reset H K hH sample.1 fallback (history.take (k.val * H)) k hprefixlen
  have hid := onlineFixedPolicy_variance_potential_noise_identity E g state
  change (∑ n ∈ Finset.range H, if hn : n < H then
      ((E ⟨n, hn⟩).transition (state n) (g ⟨n, hn⟩ (state n))).variance
        (DecisionStage.trajectoryValue (D.drop (n + 1))) else 0) =
    finiteTrajectoryVariancePotential D (state 0) -
      ∑ n ∈ Finset.range H, if hn : n < H then
        ((E ⟨n, hn⟩).transition (state n) (g ⟨n, hn⟩ (state n))).expectation
          (finiteTrajectoryVariancePotential (D.drop (n + 1))) -
            finiteTrajectoryVariancePotential (D.drop (n + 1)) (state (n + 1)) else 0 at hid
  rw [Finset.sum_range, Finset.sum_range, hstate0] at hid
  have hcost : onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 k δ c₁ c₂ =
      ∑ h : Fin H, ((E h).transition (state h.val) (g h (state h.val))).variance
        (DecisionStage.trajectoryValue (D.drop (h.val + 1))) := by
    unfold onlineActualEpisodePolicyVariance
    apply Finset.sum_congr rfl
    intro h hh
    have hr := onlineActualStageRow_eq_episodeStateAction H K hH E sample.1 fallback sample.2 k h δ c₁ c₂
    have ha := onlineT4PlayedAction_eq_selected H K hH E sample.1 fallback planner sample.2 k h
    have hr' : onlineActualStageRowSequence H K hH sample.1 fallback planner sample.2 h k.val =
      (state h.val, onlineT4PlayedAction H K hH sample.1 fallback planner sample.2 k h) := by
      simpa only [onlineT4EpisodeState, onlineT4PlayedAction, dif_pos h.isLt] using hr
    change ((E h).transition (onlineActualStageRowSequence H K hH sample.1 fallback planner sample.2 h k.val).1
      (onlineActualStageRowSequence H K hH sample.1 fallback planner sample.2 h k.val).2).variance
        (DecisionStage.trajectoryValue (stages.drop (h.val + 1))) = _
    rw [hr', ha, hD]
  have hnoise : (∑ h : Fin H, onlineVariancePotentialResidual H K hH E fallback planner k h (Real.log (1 / δ)) c₁ c₂ sample) =
      ∑ h : Fin H, (((E h).transition (state h.val) (g h (state h.val))).expectation
        (finiteTrajectoryVariancePotential (D.drop (h.val + 1))) -
          finiteTrajectoryVariancePotential (D.drop (h.val + 1)) (state (h.val + 1))) := by
    apply Finset.sum_congr rfl
    intro h hh
    have hr := onlineVariancePotentialResidual_eq_actual_noise H K hH E fallback k h (Real.log (1 / δ)) c₁ c₂ sample
    have ha := onlineT4PlayedAction_eq_selected H K hH E sample.1 fallback planner sample.2 k h
    change onlineVariancePotentialResidual H K hH E fallback planner k h (Real.log (1 / δ)) c₁ c₂ sample =
      ((E h).transition (state h.val) (onlineT4PlayedAction H K hH sample.1 fallback planner sample.2 k h)).expectation
        (finiteTrajectoryVariancePotential (stages.drop (h.val + 1))) -
          finiteTrajectoryVariancePotential (stages.drop (h.val + 1)) (state (h.val + 1)) at hr
    rw [ha, hD] at hr
    exact hr
  change _ = finiteTrajectoryVariancePotential stages (sample.1 k) - _
  rw [hcost, hnoise, hD]
  simpa only [Fin.is_lt, dif_pos] using hid
end StatisticalRL.OnlineRL

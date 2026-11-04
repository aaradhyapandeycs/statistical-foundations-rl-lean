import Formalization.Online.Regret.PolicyVariance.OnlineEpisodeVarianceRange

/-! Actual-law variance and gap proof component: OnlineEpisodeVarianceMeasurable.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance varianceMeasState : MeasurableSpace State := ⊤

theorem onlineActualEpisodePolicyVariance_measurable_end
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) (k : Fin K) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    Measurable[onlineT3CommonPrefixSigma H K (K * H) hH fallback planner ((k.val + 1) * H)]
      (fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
        onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 k δ c₁ c₂) := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let initialPot := onlineEpisodeInitialVariancePotential H K hH E fallback δ c₁ c₂ k
  let residual := fun sample => ∑ h : Fin H,
    onlineVariancePotentialResidual H K hH E fallback planner k h (Real.log (1 / δ)) c₁ c₂ sample
  have hid : (fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
      onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 k δ c₁ c₂) = initialPot - residual := by
    funext sample
    have hh := onlineActualEpisodePolicyVariance_eq_potential_sub_residuals H K hH E fallback δ c₁ c₂ k sample
    have hpolicy (history : List (OnlineMDPRow State Action H × State)) :
        onlineCappedEpisodePolicy H hH E (history.take (k.val * H)) k.val (Real.log (1 / δ)) c₁ c₂ =
          onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂ := by
      funext t s
      simp only [onlineCappedEpisodePolicy, List.take_take, Nat.min_self]
    simpa only [Pi.sub_apply, initialPot, residual, onlineEpisodeInitialVariancePotential,
      onlineEpisodeInitialVariancePotentialFromPrefix, onlineT3CommonPrefixObservation,
      onlineT3CommonFullHistory, hpolicy] using hh
  rw [hid]
  apply Measurable.sub
  · exact (onlineEpisodeInitialVariancePotential_measurable H K hH E fallback δ c₁ c₂ k).mono
      (onlineT3CommonPrefixSigma_mono H K (K * H) hH fallback planner (by nlinarith)) le_rfl
  · apply Finset.measurable_fun_sum
    intro h hh
    have hindex : k.val * H + h.val + 1 ≤ (k.val + 1) * H := by
      rw [Nat.succ_mul]
      omega
    exact (onlinePredictableObservedY_measurable_next H K (K * H) hH E fallback planner
      (k.val * H + h.val) (onlineVariancePotentialTest H K hH E k h (Real.log (1 / δ)) c₁ c₂)).mono
      (onlineT3CommonPrefixSigma_mono H K (K * H) hH fallback planner hindex) le_rfl
end StatisticalRL.OnlineRL

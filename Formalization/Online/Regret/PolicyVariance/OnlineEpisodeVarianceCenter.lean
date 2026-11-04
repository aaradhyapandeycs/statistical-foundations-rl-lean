import Formalization.Online.Regret.PolicyVariance.OnlineEpisodeVarianceMeasurable

/-! Actual-law variance and gap proof component: OnlineEpisodeVarianceCenter.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance varianceCenterState : MeasurableSpace State := ⊤
noncomputable local instance varianceCenterSample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

noncomputable def onlineEpisodeVarianceClippedMean
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) (k : Fin K)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let F := onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (k.val * H)
  onlineVarianceMeanClip ((H : ℝ)^3)
    (μ[(fun sample => onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 k δ c₁ c₂) | F] sample)

theorem onlineEpisodeVarianceClippedMean_ae_eq
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) (k : Fin K) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    onlineEpisodeVarianceClippedMean H K hH E ρ fallback δ c₁ c₂ k =ᵐ[μ]
      μ[(fun sample => onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 k δ c₁ c₂) |
        onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (k.val * H)] := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let F := onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (k.val * H)
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hn : 0 ≤ᵐ[μ] μ[(fun sample => onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 k δ c₁ c₂) | F] := by
    apply MeasureTheory.condExp_nonneg
    exact Filter.Eventually.of_forall (fun sample => (onlineActualEpisodePolicyVariance_range H K hH E sample.1 fallback sample.2 k δ c₁ c₂).1)
  have hb := onlineActualEpisodePolicyVariance_condExp_le_horizon_sq H K hH E ρ fallback δ c₁ c₂ k
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hp : (H : ℝ)^2 ≤ (H : ℝ)^3 := by nlinarith [sq_nonneg ((H : ℝ) - 1)]
  filter_upwards [hn, hb] with sample hn hb
  exact onlineVarianceMeanClip_eq _ _ hn (hb.trans hp)

theorem onlineEpisodeVariance_center_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) (k : Fin K) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let F := onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (k.val * H)
    μ[(fun sample => onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 k δ c₁ c₂ -
      onlineEpisodeVarianceClippedMean H K hH E ρ fallback δ c₁ c₂ k sample) | F] =ᵐ[μ] 0 := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let F := onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (k.val * H)
  let U := fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
    onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 k δ c₁ c₂
  let C := onlineEpisodeVarianceClippedMean H K hH E ρ fallback δ c₁ c₂ k
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hF : F ≤ (⊤ : MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))) := le_top
  have hc : C =ᵐ[μ] μ[U | F] := onlineEpisodeVarianceClippedMean_ae_eq H K hH E ρ fallback δ c₁ c₂ k
  have hce : μ[C | F] =ᵐ[μ] μ[U | F] := by
    have h := MeasureTheory.condExp_congr_ae (m := F) hc
    rw [MeasureTheory.condExp_of_stronglyMeasurable hF MeasureTheory.stronglyMeasurable_condExp Integrable.of_finite] at h
    exact h
  have hs := MeasureTheory.condExp_sub (μ := μ) (f := U) (g := C) Integrable.of_finite Integrable.of_finite F
  filter_upwards [hs, hce] with sample hs hc
  change μ[U - C | F] sample = 0
  rw [hs]
  simp only [Pi.sub_apply, hc, sub_self]
end StatisticalRL.OnlineRL

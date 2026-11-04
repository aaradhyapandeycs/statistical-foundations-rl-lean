import Formalization.Online.Regret.PolicyVariance.OnlineEpisodeVarianceCenter

/-! Actual-law variance and gap proof component: OnlineEpisodeVarianceProcess.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance varianceProcessState : MeasurableSpace State := ⊤
noncomputable local instance varianceProcessSample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

noncomputable def onlineVariancePaddedY
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  if hn : n < K then
    onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 ⟨n, hn⟩ δ c₁ c₂ -
      onlineEpisodeVarianceClippedMean H K hH E ρ fallback δ c₁ c₂ ⟨n, hn⟩ sample
  else 0

theorem onlineVariancePaddedY_abs_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    |onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ n sample| ≤ (H : ℝ)^3 := by
  unfold onlineVariancePaddedY
  split_ifs with hn
  · apply abs_le.mpr
    exact onlineVarianceCentered_mem _ _ _ (by positivity)
      (onlineActualEpisodePolicyVariance_range H K hH E sample.1 fallback sample.2 ⟨n, hn⟩ δ c₁ c₂)
  · simp

theorem onlineVariancePaddedY_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) (n : ℕ) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ n |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (n * H)] =ᵐ[μ] 0 := by
  dsimp
  by_cases hn : n < K
  · have heq : onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ n =
      fun sample => onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 ⟨n, hn⟩ δ c₁ c₂ -
        onlineEpisodeVarianceClippedMean H K hH E ρ fallback δ c₁ c₂ ⟨n, hn⟩ sample := by
      funext sample
      simp only [onlineVariancePaddedY, dif_pos hn]
    rw [heq]
    exact onlineEpisodeVariance_center_condExp_zero H K hH E ρ fallback δ c₁ c₂ ⟨n, hn⟩
  · have heq : onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ n = 0 := by
      funext sample
      simp only [onlineVariancePaddedY, dif_neg hn, Pi.zero_apply]
    rw [heq, condExp_zero]

theorem onlineVariancePaddedY_adapted
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    Adapted (onlineT4EpisodeFiltration H K hH fallback planner)
      (onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂) := by
  dsimp
  intro n
  by_cases hn : n < K
  · let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let F := onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (n * H)
    have hm : Measurable[F] (onlineEpisodeVarianceClippedMean H K hH E ρ fallback δ c₁ c₂ ⟨n, hn⟩) := by
      unfold onlineEpisodeVarianceClippedMean onlineVarianceMeanClip
      exact measurable_const.max (measurable_const.min MeasureTheory.stronglyMeasurable_condExp.measurable)
    have hmono : F ≤ onlineT3CommonPrefixSigma H K (K * H) hH fallback planner ((n + 1) * H) :=
      onlineT3CommonPrefixSigma_mono H K (K * H) hH fallback planner (by nlinarith)
    have hu := onlineActualEpisodePolicyVariance_measurable_end H K hH E fallback δ c₁ c₂ ⟨n, hn⟩
    have heq : onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ n =
      fun sample => onlineActualEpisodePolicyVariance H K hH E sample.1 fallback sample.2 ⟨n, hn⟩ δ c₁ c₂ -
        onlineEpisodeVarianceClippedMean H K hH E ρ fallback δ c₁ c₂ ⟨n, hn⟩ sample := by
      funext sample
      simp only [onlineVariancePaddedY, dif_pos hn]
    rw [heq]
    exact (hu.sub (hm.mono hmono le_rfl)).stronglyMeasurable
  · have heq : onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ n = 0 := by
      funext sample
      simp only [onlineVariancePaddedY, dif_neg hn, Pi.zero_apply]
    rw [heq]
    exact stronglyMeasurable_const
end StatisticalRL.OnlineRL

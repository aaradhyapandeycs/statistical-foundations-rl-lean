import Formalization.Online.Regret.PolicyVariance.OnlineEpisodeVarianceProcess

/-! Actual-law variance and gap proof component: OnlineEpisodeVarianceMGF.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance varianceMGFStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance varianceMGFSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable

theorem onlineVariancePaddedY_hasCondSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (δ c₁ c₂ : ℝ) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) (K * H)).rowMeasure
    let ℱ := onlineT4EpisodeFiltration H K hH fallback (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)
    HasCondSubgaussianMGF (ℱ n) (ℱ.le n)
      (onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ (n + 1)) ((H : ℝ≥0)^6) μ := by
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let ℱ := onlineT4EpisodeFiltration H K hH fallback (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)
  let Y := onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂
  have hY : Measurable (Y (n + 1)) :=
    (onlineVariancePaddedY_adapted H K hH E ρ fallback δ c₁ c₂ (n + 1)).measurable.mono
      (ℱ.le (n + 1)) le_rfl
  have hbound : ∀ sample, Y (n + 1) sample ∈ Set.Icc (-((H : ℝ)^3)) ((H : ℝ)^3) := by
    intro sample
    exact abs_le.mp (onlineVariancePaddedY_abs_le H K hH E ρ fallback δ c₁ c₂ (n + 1) sample)
  have hcenter : μ[Y (n + 1) | ℱ n] =ᵐ[μ] 0 := by
    exact onlineVariancePaddedY_condExp_zero H K hH E ρ fallback δ c₁ c₂ (n + 1)
  have hs := StatisticalRL.hasCondSubgaussianMGF_of_pointwise_Icc_condExp_zero
    μ (ℱ n) (ℱ.le n) (Y (n + 1)) hY (-((H : ℝ)^3)) ((H : ℝ)^3) hbound hcenter
  have hw : ((‖(H : ℝ)^3 - (-((H : ℝ)^3))‖₊ / 2)^2) = (H : ℝ≥0)^6 := by
    apply NNReal.eq
    change (‖(H : ℝ)^3 - (-((H : ℝ)^3))‖ / 2)^2 = (H : ℝ)^6
    have hh : 0 ≤ (H : ℝ)^3 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    ring
  simpa only [hw] using hs

theorem onlineVariancePaddedY_hasSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) (K * H)).rowMeasure
    HasSubgaussianMGF (onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ n) ((H : ℝ≥0)^6) μ := by
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hm := (onlineVariancePaddedY_adapted H K hH E ρ fallback δ c₁ c₂ n).measurable.mono
    ((onlineT4EpisodeFiltration H K hH fallback (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)).le n) le_rfl
  have hb : ∀ sample, onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ n sample ∈
      Set.Icc (-((H : ℝ)^3)) ((H : ℝ)^3) := by
    intro sample
    exact abs_le.mp (onlineVariancePaddedY_abs_le H K hH E ρ fallback δ c₁ c₂ n sample)
  have hz : ∫ sample, onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ n sample ∂μ = 0 := by
    have hF : onlineT3CommonPrefixSigma H K (K * H) hH fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) (n * H) ≤
        (StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable : MeasurableSpace
          ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))) := le_top
    rw [← integral_condExp hF]
    have hc := onlineVariancePaddedY_condExp_zero H K hH E ρ fallback δ c₁ c₂ n
    simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hc
  have hs := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm.aemeasurable
    (Filter.Eventually.of_forall hb) hz
  have hw : ((‖(H : ℝ)^3 - (-((H : ℝ)^3))‖₊ / 2)^2) = (H : ℝ≥0)^6 := by
    apply NNReal.eq
    change (‖(H : ℝ)^3 - (-((H : ℝ)^3))‖ / 2)^2 = (H : ℝ)^6
    have hh : 0 ≤ (H : ℝ)^3 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    ring
  simpa only [hw] using hs

theorem onlineVarianceEpisodeSum_hasSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) (K * H)).rowMeasure
    HasSubgaussianMGF
      (fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
        ∑ n ∈ Finset.range K, onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ n sample)
      ((K : ℝ≥0) * (H : ℝ≥0)^6) μ := by
  dsimp
  have hs := HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF
    (cY := fun _ => (H : ℝ≥0)^6)
    (onlineVariancePaddedY_adapted H K hH E ρ fallback δ c₁ c₂)
    (onlineVariancePaddedY_hasSubgaussianMGF H K hH E ρ fallback δ c₁ c₂ 0) K
    (fun n _hn => onlineVariancePaddedY_hasCondSubgaussianMGF H K hH E ρ fallback δ c₁ c₂ n)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hs
end StatisticalRL.OnlineRL

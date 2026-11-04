import Formalization.Online.Regret.PolicyVariance.OnlineEpisodeVarianceSumBridge
import Formalization.Probability.FiniteStrictTwoSidedTail

/-! Actual-law variance and gap proof component: OnlineT6PolicyConfidence.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance varianceConfidenceState : MeasurableSpace State := ⊤
noncomputable local instance varianceConfidenceSample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

theorem onlineActualT6Policy_confidence_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    1 - 2 * δ < μ.real {sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) |
      onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤
        (K : ℝ) * (H : ℝ)^2 + Real.sqrt (2 * ((K : ℝ) * (H : ℝ)^6) * Real.log (1 / δ))} := by
  dsimp
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let X := fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
    ∑ n ∈ Finset.range K, onlineVariancePaddedY H K hH E ρ fallback δ c₁ c₂ n sample
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hc : 0 < (K : ℝ≥0) * (H : ℝ≥0)^6 := by
    have hK' : 0 < (K : ℝ≥0) := by exact_mod_cast hK
    have hH' : 0 < (H : ℝ≥0) := by exact_mod_cast hH
    exact mul_pos hK' (pow_pos hH' _)
  have ht := StatisticalRL.HasSubgaussianMGF.measure_abs_le_sqrt_gt_of_finite
    μ X ((K : ℝ≥0) * (H : ℝ≥0)^6) hc
    (onlineVarianceEpisodeSum_hasSubgaussianMGF H K hH E ρ fallback δ c₁ c₂) δ hδ hδ1
  have hsub : {sample | |X sample| ≤ Real.sqrt (2 * ((K : ℝ) * (H : ℝ)^6) * Real.log (1 / δ))} ≤ᵐ[μ]
      {sample | onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤
        (K : ℝ) * (H : ℝ)^2 + Real.sqrt (2 * ((K : ℝ) * (H : ℝ)^6) * Real.log (1 / δ))} := by
    filter_upwards [onlineActualT6Policy_le_centered_sum_ae H K hH E ρ fallback δ c₁ c₂] with sample hb hs
    have hx : X sample ≤ Real.sqrt (2 * ((K : ℝ) * (H : ℝ)^6) * Real.log (1 / δ)) :=
      (le_abs_self _).trans hs
    dsimp [X] at hx
    change onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤
      (K : ℝ) * (H : ℝ)^2 + Real.sqrt (2 * ((K : ℝ) * (H : ℝ)^6) * Real.log (1 / δ))
    linarith
  have hm := measure_mono_ae hsub
  have hmreal := ENNReal.toReal_mono (measure_ne_top μ _) hm
  have ht' : 1 - 2 * δ < μ.real {sample | |X sample| ≤ Real.sqrt (2 * ((K : ℝ) * (H : ℝ)^6) * Real.log (1 / δ))} := by
    simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] using ht
  exact ht'.trans_le hmreal
end StatisticalRL.OnlineRL

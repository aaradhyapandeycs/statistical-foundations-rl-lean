import Formalization.Online.Regret.T8.OnlineT8SourceRadius

/-! Actual-law variance and gap proof component: OnlineT8SourceConfidence.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t8ConfidenceState : MeasurableSpace State := ⊤
noncomputable local instance t8ConfidenceSample (H K : ℕ) : MeasurableSpace
    ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

theorem onlineActualT8_source_confidence
    (H K : ℕ) (hH : 0 < H) (hN : 2 ≤ K * H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    1 - 2 * (Nat.log2 (K * H) : ℝ) * δ ≤ μ.real
      {sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) |
        |onlineActualT8 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤
          Real.sqrt (32 * (H : ℝ)^2 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ)) +
            5 * (H : ℝ)^2 * Real.log (1 / δ)} := by
  classical
  dsimp
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let μ : Measure ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := onlineT8PaddedY H K hH E fallback planner (Real.log (1 / δ)) c₁ c₂
  let j := Nat.log2 (K * H)
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hL : 0 ≤ Real.log (1 / δ) := le_trans (by norm_num) (onlineT3_sourceLog_ge_two δ hδ hδsmall)
  by_cases hb : 2 * (j : ℝ) * δ < 1
  · have hp := onlineT8_source_first_radius_probability H K j hH hN E ρ fallback planner c₁ c₂ δ
      hc₁ hc₂ hδ hδsmall rfl hb
    have hv := onlineT8PredictableSecondMomentSum_le_actualT6UCB H K hH E ρ fallback δ c₁ c₂ hL hc₁ hc₂
    have hsub : onlineFreedmanSourceRadiusSet μ ℱ X (K * H) ((H : ℝ)^2) (Real.log (1 / δ)) ≤ᵐ[μ]
      {sample | |onlineActualT8 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤
          Real.sqrt (32 * (H : ℝ)^2 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ)) +
            5 * (H : ℝ)^2 * Real.log (1 / δ)} := by
      filter_upwards [hv] with sample hv hs
      have hmul : 8 * predictableSecondMomentSum μ ℱ X (K * H) sample * Real.log (1 / δ) ≤
          32 * (H : ℝ)^2 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hv) hL]
      have hroot := Real.sqrt_le_sqrt hmul
      change |incrementSum X (K * H) sample| ≤ _ at hs
      change |onlineActualT8 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤ _
      rw [show incrementSum X (K * H) sample = onlineActualT8 H K hH E sample.1 fallback sample.2 δ c₁ c₂ by
        exact onlineT8PaddedY_sum_eq_actualT8 H K hH E sample.1 fallback sample.2 δ c₁ c₂] at hs
      linarith
    have hm := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    exact hp.trans hm
  · have hnon : 0 ≤ μ.real {sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) |
        |onlineActualT8 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤
          Real.sqrt (32 * (H : ℝ)^2 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ)) +
            5 * (H : ℝ)^2 * Real.log (1 / δ)} := ENNReal.toReal_nonneg
    linarith
end StatisticalRL.OnlineRL

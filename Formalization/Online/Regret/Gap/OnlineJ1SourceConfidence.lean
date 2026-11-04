import Formalization.Online.Regret.Gap.OnlineJ1ActualSum

/-! Actual-law variance and gap proof component: OnlineJ1SourceConfidence.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance j1ConfidenceState : MeasurableSpace State := ⊤
noncomputable local instance j1ConfidenceSample (H K : ℕ) : MeasurableSpace
    ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

theorem onlineActualJ1_source_confidence_conditional
    (H K : ℕ) (hH : 0 < H) (hN : 2 ≤ K * H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    1 - 2 * (Nat.log2 (K * H) : ℝ) * δ ≤ μ.real
      {sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) |
        onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
          (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2) →
        |onlineActualJ1 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤
          Real.sqrt (8 * onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ)) +
            5 * (H : ℝ) * Real.log (1 / δ)} := by
  classical
  dsimp
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let μ : Measure ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := onlineJ1PaddedY H K hH E fallback (Real.log (1 / δ)) c₁ c₂
  let j := Nat.log2 (K * H)
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hL : 0 ≤ Real.log (1 / δ) := le_trans (by norm_num) (onlineT3_sourceLog_ge_two δ hδ hδsmall)
  by_cases hb : 2 * (j : ℝ) * δ < 1
  · have hp := onlineJ1_source_first_radius_probability H K j hH hN E ρ fallback c₁ c₂ δ
      hc₁ hc₂ hδ hδsmall rfl hb
    have hv := onlineJ1PredictableSecondMomentSum_le_actualT6Difference H K hH E ρ fallback δ c₁ c₂
    have hsub : onlineFreedmanSourceRadiusSet μ ℱ X (K * H) (H : ℝ) (Real.log (1 / δ)) ≤ᵐ[μ]
      {sample | onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
          (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2) →
        |onlineActualJ1 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤
          Real.sqrt (8 * onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ)) +
            5 * (H : ℝ) * Real.log (1 / δ)} := by
      filter_upwards [hv] with sample hv hs
      intro hoptimism
      have hmul : 8 * predictableSecondMomentSum μ ℱ X (K * H) sample * Real.log (1 / δ) ≤
          8 * onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hv) hL]
      have hroot := Real.sqrt_le_sqrt hmul
      change |incrementSum X (K * H) sample| ≤ _ at hs
      change |onlineActualJ1 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤ _
      rw [show incrementSum X (K * H) sample = onlineActualJ1 H K hH E sample.1 fallback sample.2 δ c₁ c₂ by
        exact onlineJ1PaddedY_sum_eq_actualJ1_on_optimism H K hH E sample.1 fallback sample.2 δ c₁ c₂ hL hc₁ hc₂ hoptimism] at hs
      linarith
    have hm := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    exact hp.trans hm
  · have hnon : 0 ≤ μ.real {sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) |
        onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
          (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2) →
        |onlineActualJ1 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤
          Real.sqrt (8 * onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂ * Real.log (1 / δ)) +
            5 * (H : ℝ) * Real.log (1 / δ)} := ENNReal.toReal_nonneg
    linarith
end StatisticalRL.OnlineRL

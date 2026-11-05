import Formalization.Online.Regret.MVP.T34.MVPActualT3Tail
import Formalization.Online.Regret.MVP.T34.MVPActualT3Sum
import Formalization.Online.Regret.MVP.T34.MVPActualT3VarianceSum
import Formalization.Online.Regret.MVP.T6.MVPActualT8SourceConfidence
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance mvpT3ConfidenceState : MeasurableSpace State := ⊤
noncomputable local instance mvpT3ConfidenceSample (H K : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) := ⊤
theorem mvpActualT3_independent_tail_confidence
    (H K : ℕ) (hH : 0 < H) (hN : 2 ≤ K * H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δplan δtail c₁ c₂ : ℝ)
    (hδplan : 0 < δplan) (hδsmall : δplan ≤ 1 / 100)
    (hδtail : 0 < δtail) (hδtailsmall : δtail ≤ 1 / 100) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δplan)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    1 - 2 * (Nat.log2 (K * H) : ℝ) * δtail ≤ μ.real
      {sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) |
        |mvpActualT3 H K hH E sample.1 fallback sample.2 δplan c₁ c₂| ≤
          Real.sqrt (8 * mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δplan c₁ c₂ * Real.log (1 / δtail)) +
            5 * (H : ℝ) * Real.log (1 / δtail)} := by
  classical
  dsimp
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δplan)) c₁ c₂
  let μ : Measure ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := mvpT3PaddedY H K hH E fallback planner (Real.log (1 / δplan)) c₁ c₂
  let j := Nat.log2 (K * H)
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hL : 0 ≤ Real.log (1 / δplan) := le_trans (by norm_num) (onlineT3_sourceLog_ge_two δplan hδplan hδsmall)
  have hLtail : 0 ≤ Real.log (1 / δtail) := le_trans (by norm_num) (onlineT3_sourceLog_ge_two δtail hδtail hδtailsmall)
  by_cases hb : 2 * (j : ℝ) * δtail < 1
  · have hp := mvpT3_independent_tail_source_radius_probability H K j hH hN E ρ fallback planner
      (Real.log (1 / δplan)) c₁ c₂ δtail hL hc₁ hc₂ hδtail hδtailsmall rfl hb
    have hv := mvpT3PredictableSecondMomentSum_eq_actualT6UCB H K hH E ρ fallback δplan c₁ c₂
    have hsub : onlineFreedmanSourceRadiusSet μ ℱ X (K * H) ((H : ℝ)) (Real.log (1 / δtail)) ≤ᵐ[μ]
      {sample | |mvpActualT3 H K hH E sample.1 fallback sample.2 δplan c₁ c₂| ≤
          Real.sqrt (8 * mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δplan c₁ c₂ * Real.log (1 / δtail)) +
            5 * (H : ℝ) * Real.log (1 / δtail)} := by
      filter_upwards [hv] with sample hv hs
      have hroot : Real.sqrt (8 * predictableSecondMomentSum μ ℱ X (K * H) sample * Real.log (1 / δtail)) =
          Real.sqrt (8 * mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δplan c₁ c₂ * Real.log (1 / δtail)) := by
        rw [hv]
      change |incrementSum X (K * H) sample| ≤ _ at hs
      change |mvpActualT3 H K hH E sample.1 fallback sample.2 δplan c₁ c₂| ≤ _
      rw [show incrementSum X (K * H) sample = mvpActualT3 H K hH E sample.1 fallback sample.2 δplan c₁ c₂ by
        exact mvpT3PaddedY_sum_eq_actualT3 H K hH E sample.1 fallback sample.2 δplan c₁ c₂] at hs
      linarith
    have hm := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    exact hp.trans hm
  · have hnon : 0 ≤ μ.real {sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) |
        |mvpActualT3 H K hH E sample.1 fallback sample.2 δplan c₁ c₂| ≤
          Real.sqrt (8 * mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δplan c₁ c₂ * Real.log (1 / δtail)) +
            5 * (H : ℝ) * Real.log (1 / δtail)} := ENNReal.toReal_nonneg
    linarith
end StatisticalRL.OnlineRL

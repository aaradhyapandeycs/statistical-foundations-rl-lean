import Formalization.Online.Regret.T4.OnlineRegretT4EpisodeProcess

/-! actual whole-episode Azuma MGF. The conditional MGF premise
is derived from the actual block centering and the pathwise H bound. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t4AzumaStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t4AzumaSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable

theorem onlineT4PaddedEpisodeY_hasCondSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT4EpisodeFiltration H K hH fallback planner
    HasCondSubgaussianMGF (ℱ n) (ℱ.le n)
      (onlineT4PaddedEpisodeY H K hH E fallback planner (n + 1)) ((H : ℝ≥0)^2) μ := by
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let ℱ := onlineT4EpisodeFiltration H K hH fallback planner
  let Y := onlineT4PaddedEpisodeY H K hH E fallback planner
  have hY : Measurable (Y (n + 1)) :=
    (onlineT4PaddedEpisodeY_adapted H K hH E fallback planner (n + 1)).measurable.mono
      (ℱ.le (n + 1)) le_rfl
  have hbound : ∀ sample, Y (n + 1) sample ∈ Set.Icc (-(H : ℝ)) (H : ℝ) := by
    intro sample
    exact abs_le.mp (onlineT4PaddedEpisodeY_abs_le H K hH E fallback planner (n + 1) sample)
  have hcenter : μ[Y (n + 1) | ℱ n] =ᵐ[μ] 0 := by
    exact onlineT4PaddedEpisodeY_condExp_zero H K hH E ρ fallback planner (n + 1)
  have hs := StatisticalRL.hasCondSubgaussianMGF_of_pointwise_Icc_condExp_zero
    μ (ℱ n) (ℱ.le n) (Y (n + 1)) hY (-(H : ℝ)) (H : ℝ) hbound hcenter
  simpa only [onlineT4HoeffdingWidth] using hs

theorem onlineT4EpisodeSum_hasSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    HasSubgaussianMGF
      (fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
        ∑ n ∈ Finset.range K, onlineT4PaddedEpisodeY H K hH E fallback planner n sample)
      ((K : ℝ≥0) * (H : ℝ≥0)^2) μ := by
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hs := HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF
    (μ := μ) (cY := fun _ => (H : ℝ≥0)^2)
    (onlineT4PaddedEpisodeY_adapted H K hH E fallback planner)
    (onlineT4PaddedEpisodeY_hasSubgaussianMGF H K hH E ρ fallback planner 0) K
    (fun n _hn => onlineT4PaddedEpisodeY_hasCondSubgaussianMGF H K hH E ρ fallback planner n)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hs

end StatisticalRL.OnlineRL

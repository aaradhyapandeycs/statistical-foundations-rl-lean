import Formalization.Online.Regret.T4.OnlineT4SuffixProcess

/-! Same-experiment suffix proof component: OnlineT4SuffixAzuma.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance suffixT4AzumaStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance suffixT4AzumaSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable

theorem onlineT4SuffixPaddedEpisodeY_hasCondSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (j : Fin H) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT4EpisodeFiltration H K hH fallback planner
    HasCondSubgaussianMGF (ℱ n) (ℱ.le n)
      (onlineT4SuffixPaddedEpisodeY H K hH E fallback planner j (n + 1)) ((H : ℝ≥0)^2) μ := by
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let ℱ := onlineT4EpisodeFiltration H K hH fallback planner
  let Y := onlineT4SuffixPaddedEpisodeY H K hH E fallback planner j
  have hY : Measurable (Y (n + 1)) :=
    (onlineT4SuffixPaddedEpisodeY_adapted H K hH E fallback planner j (n + 1)).measurable.mono
      (ℱ.le (n + 1)) le_rfl
  have hbound : ∀ sample, Y (n + 1) sample ∈ Set.Icc (-(H : ℝ)) (H : ℝ) := by
    intro sample
    exact abs_le.mp (onlineT4SuffixPaddedEpisodeY_abs_le H K hH E fallback planner j (n + 1) sample)
  have hcenter : μ[Y (n + 1) | ℱ n] =ᵐ[μ] 0 := by
    exact onlineT4SuffixPaddedEpisodeY_condExp_zero H K hH E ρ fallback planner j (n + 1)
  have hs := StatisticalRL.hasCondSubgaussianMGF_of_pointwise_Icc_condExp_zero
    μ (ℱ n) (ℱ.le n) (Y (n + 1)) hY (-(H : ℝ)) (H : ℝ) hbound hcenter
  simpa only [onlineT4HoeffdingWidth] using hs

theorem onlineT4SuffixEpisodeSum_hasSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (j : Fin H) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    HasSubgaussianMGF
      (fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
        ∑ n ∈ Finset.range K, onlineT4SuffixPaddedEpisodeY H K hH E fallback planner j n sample)
      ((K : ℝ≥0) * (H : ℝ≥0)^2) μ := by
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hs := HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF
    (μ := μ) (cY := fun _ => (H : ℝ≥0)^2)
    (onlineT4SuffixPaddedEpisodeY_adapted H K hH E fallback planner j)
    (onlineT4SuffixPaddedEpisodeY_hasSubgaussianMGF H K hH E ρ fallback planner j 0) K
    (fun n _hn => onlineT4SuffixPaddedEpisodeY_hasCondSubgaussianMGF H K hH E ρ fallback planner j n)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hs

end StatisticalRL.OnlineRL

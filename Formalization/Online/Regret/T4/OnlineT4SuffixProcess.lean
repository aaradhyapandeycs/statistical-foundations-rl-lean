import Formalization.Online.Regret.T4.OnlineT4SuffixCentering
import Formalization.Online.Regret.T4.OnlineRegretT4EpisodeProcess
import Formalization.Probability.ConditionalHoeffding

/-! Same-experiment suffix proof component: OnlineT4SuffixProcess.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance suffixT4ProcessStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance suffixT4ProcessSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable

noncomputable def onlineT4SuffixPaddedEpisodeY
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (j : Fin H) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  if hn : n < K then
    onlineT4SuffixEpisodeIncrement H K hH E fallback planner j.val ⟨n, hn⟩ sample
  else 0

theorem onlineT4SuffixPaddedEpisodeY_eq_of_lt
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (j : Fin H) (n : ℕ) (hn : n < K) :
    onlineT4SuffixPaddedEpisodeY H K hH E fallback planner j n =
      fun sample => onlineT4SuffixEpisodeIncrement H K hH E fallback planner j.val ⟨n, hn⟩ sample := by
  funext sample
  simp only [onlineT4SuffixPaddedEpisodeY, dif_pos hn]

theorem onlineT4SuffixPaddedEpisodeY_eq_zero_of_ge
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (j : Fin H) (n : ℕ) (hn : ¬n < K) :
    onlineT4SuffixPaddedEpisodeY H K hH E fallback planner j n = 0 := by
  funext sample
  simp only [onlineT4SuffixPaddedEpisodeY, dif_neg hn, Pi.zero_apply]

theorem onlineT4SuffixPaddedEpisodeY_adapted
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (j : Fin H) :
    Adapted (onlineT4EpisodeFiltration H K hH fallback planner)
      (onlineT4SuffixPaddedEpisodeY H K hH E fallback planner j) := by
  intro n
  by_cases hn : n < K
  · rw [onlineT4SuffixPaddedEpisodeY_eq_of_lt H K hH E fallback planner j n hn]
    exact (onlineT4SuffixEpisodeIncrement_measurable_end H K hH E fallback planner j.val
      ⟨n, hn⟩).stronglyMeasurable
  · rw [onlineT4SuffixPaddedEpisodeY_eq_zero_of_ge H K hH E fallback planner j n hn]
    exact stronglyMeasurable_const

theorem onlineT4SuffixPaddedEpisodeY_abs_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (j : Fin H)
    (n : ℕ) (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    |onlineT4SuffixPaddedEpisodeY H K hH E fallback planner j n sample| ≤ (H : ℝ) := by
  unfold onlineT4SuffixPaddedEpisodeY
  split_ifs with hn
  · exact onlineT4SuffixEpisodeIncrement_abs_le H K hH E fallback planner j.val j.isLt.le ⟨n, hn⟩ sample
  · simp

theorem onlineT4SuffixPaddedEpisodeY_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (j : Fin H) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[onlineT4SuffixPaddedEpisodeY H K hH E fallback planner j n |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (n * H)] =ᵐ[μ] 0 := by
  dsimp
  by_cases hn : n < K
  · rw [onlineT4SuffixPaddedEpisodeY_eq_of_lt H K hH E fallback planner j n hn]
    exact onlineT4SuffixEpisodeIncrement_condExp_zero H K hH E ρ fallback planner j.val ⟨n, hn⟩
  · rw [onlineT4SuffixPaddedEpisodeY_eq_zero_of_ge H K hH E fallback planner j n hn, condExp_zero]

theorem onlineT4SuffixPaddedEpisodeY_integral_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (j : Fin H) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    ∫ sample, onlineT4SuffixPaddedEpisodeY H K hH E fallback planner j n sample ∂μ = 0 := by
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hm : onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (n * H) ≤
      (StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable :
        MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))) := le_top
  rw [← integral_condExp hm]
  have hc := onlineT4SuffixPaddedEpisodeY_condExp_zero H K hH E ρ fallback planner j n
  simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hc

theorem onlineT4SuffixPaddedEpisodeY_hasSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (j : Fin H) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    HasSubgaussianMGF (onlineT4SuffixPaddedEpisodeY H K hH E fallback planner j n) ((H : ℝ≥0)^2) μ := by
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hm := (onlineT4SuffixPaddedEpisodeY_adapted H K hH E fallback planner j n).measurable.mono
    ((onlineT4EpisodeFiltration H K hH fallback planner).le n) le_rfl
  have hb : ∀ sample, onlineT4SuffixPaddedEpisodeY H K hH E fallback planner j n sample ∈
      Set.Icc (-(H : ℝ)) (H : ℝ) := by
    intro sample
    exact abs_le.mp (onlineT4SuffixPaddedEpisodeY_abs_le H K hH E fallback planner j n sample)
  have hs := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm.aemeasurable
    (Filter.Eventually.of_forall hb)
    (onlineT4SuffixPaddedEpisodeY_integral_zero H K hH E ρ fallback planner j n)
  simpa only [onlineT4HoeffdingWidth] using hs

end StatisticalRL.OnlineRL

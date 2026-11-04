import Formalization.Online.Regret.T4.OnlineRegretT4EpisodeCentering
import Formalization.Probability.ConditionalHoeffding

/-! actual whole-episode process, conditional Hoeffding, and
Azuma MGF. Every random increment is the source return minus the value of
the policy selected from the completed pre-episode history. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t4ProcessStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t4ProcessSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable

noncomputable def onlineT4PaddedEpisodeY
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  if hn : n < K then
    onlineT4EpisodeIncrement H K hH E sample.1 fallback planner sample.2 ⟨n, hn⟩
  else 0

noncomputable def onlineT4EpisodeFiltration
    (H K : ℕ) (hH : 0 < H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) :
    Filtration ℕ (StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable :
      MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))) where
  seq n := onlineT3CommonPrefixSigma H K (K * H) hH fallback planner ((n + 1) * H)
  mono' := by
    intro n m hnm
    exact onlineT3CommonPrefixSigma_mono H K (K * H) hH fallback planner
      (Nat.mul_le_mul_right H (Nat.add_le_add_right hnm 1))
  le' _ := le_top

theorem onlineT4PaddedEpisodeY_eq_of_lt
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (n : ℕ) (hn : n < K) :
    onlineT4PaddedEpisodeY H K hH E fallback planner n =
      fun sample => onlineT4EpisodeIncrement H K hH E sample.1 fallback planner sample.2
        ⟨n, hn⟩ := by
  funext sample
  simp only [onlineT4PaddedEpisodeY, dif_pos hn]

theorem onlineT4PaddedEpisodeY_eq_zero_of_ge
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (n : ℕ) (hn : ¬n < K) :
    onlineT4PaddedEpisodeY H K hH E fallback planner n = 0 := by
  funext sample
  simp only [onlineT4PaddedEpisodeY, dif_neg hn, Pi.zero_apply]

theorem onlineT4PaddedEpisodeY_adapted
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) :
    Adapted (onlineT4EpisodeFiltration H K hH fallback planner)
      (onlineT4PaddedEpisodeY H K hH E fallback planner) := by
  intro n
  by_cases hn : n < K
  · rw [onlineT4PaddedEpisodeY_eq_of_lt H K hH E fallback planner n hn]
    exact (onlineT4EpisodeIncrement_measurable_end H K hH E fallback planner
      ⟨n, hn⟩).stronglyMeasurable
  · rw [onlineT4PaddedEpisodeY_eq_zero_of_ge H K hH E fallback planner n hn]
    exact stronglyMeasurable_const

theorem onlineT4PaddedEpisodeY_abs_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (n : ℕ) (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    |onlineT4PaddedEpisodeY H K hH E fallback planner n sample| ≤ (H : ℝ) := by
  unfold onlineT4PaddedEpisodeY
  split_ifs with hn
  · exact onlineT4EpisodeIncrement_abs_le H K hH E sample.1 fallback planner sample.2 ⟨n, hn⟩
  · simp

theorem onlineT4PaddedEpisodeY_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[onlineT4PaddedEpisodeY H K hH E fallback planner n |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (n * H)] =ᵐ[μ] 0 := by
  dsimp
  by_cases hn : n < K
  · rw [onlineT4PaddedEpisodeY_eq_of_lt H K hH E fallback planner n hn]
    exact onlineT4EpisodeIncrement_condExp_zero H K hH E ρ fallback planner ⟨n, hn⟩
  · rw [onlineT4PaddedEpisodeY_eq_zero_of_ge H K hH E fallback planner n hn, condExp_zero]

theorem onlineT4PaddedEpisodeY_integral_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    ∫ sample, onlineT4PaddedEpisodeY H K hH E fallback planner n sample ∂μ = 0 := by
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hm : onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (n * H) ≤
      (StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable :
        MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))) := le_top
  rw [← integral_condExp hm]
  have hc := onlineT4PaddedEpisodeY_condExp_zero H K hH E ρ fallback planner n
  simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hc

theorem onlineT4HoeffdingWidth (H : ℕ) :
    ((‖(H : ℝ) - (-(H : ℝ))‖₊ / 2)^2) = (H : ℝ≥0)^2 := by
  apply NNReal.eq
  change (‖(H : ℝ) - (-(H : ℝ))‖ / 2)^2 = (H : ℝ)^2
  rw [Real.norm_eq_abs, abs_of_nonneg (by have hp : 0 ≤ (H : ℝ) := Nat.cast_nonneg H; linarith)]
  ring

theorem onlineT4PaddedEpisodeY_hasSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    HasSubgaussianMGF (onlineT4PaddedEpisodeY H K hH E fallback planner n) ((H : ℝ≥0)^2) μ := by
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hm := (onlineT4PaddedEpisodeY_adapted H K hH E fallback planner n).measurable.mono
    ((onlineT4EpisodeFiltration H K hH fallback planner).le n) le_rfl
  have hb : ∀ sample, onlineT4PaddedEpisodeY H K hH E fallback planner n sample ∈
      Set.Icc (-(H : ℝ)) (H : ℝ) := by
    intro sample
    exact abs_le.mp (onlineT4PaddedEpisodeY_abs_le H K hH E fallback planner n sample)
  have hs := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm.aemeasurable
    (Filter.Eventually.of_forall hb)
    (onlineT4PaddedEpisodeY_integral_zero H K hH E ρ fallback planner n)
  simpa only [onlineT4HoeffdingWidth] using hs

end StatisticalRL.OnlineRL

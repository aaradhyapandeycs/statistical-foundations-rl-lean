import Formalization.Online.Regret.T3.OnlineT3SuffixActualEpisodeFamily
import Formalization.Online.Regret.T3.OnlineRegretT3SourceBound
import Formalization.Probability.OnlineVarianceRadiusAlgebra

/-! Deterministic T₆-UCB radius comparison for the simultaneous source suffix
array event. This is a pointwise extension of the already proved actual-law
suffix event, not another concentration estimate. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory

universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t3SuffixExpandedStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t3SuffixExpandedSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t3SuffixExpandedStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t3SuffixExpandedActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The all-suffix source episode array event with the expanded policy and
transition-difference radius used by the source stage-one consumer. -/
noncomputable def onlineT3AllSuffixActualEpisodeArrayExpandedRadiusSet
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (c₁ c₂ δ' : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  {sample | ∀ j : Fin H,
    |onlineT3ActualSuffixEpisodeArray H K hH E sample.1 fallback sample.2 δ' c₁ c₂ j| ≤
      4 * Real.sqrt (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
        Real.log (1 / δ')) +
      4 * Real.sqrt (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
        Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ')}

/-- Every point in the T₆-UCB radius event obeys the expanded radius, for
all source suffix starts. -/
theorem onlineT3AllSuffixActualEpisodeArrayRadiusSet_subset_expanded
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (c₁ c₂ δ' : ℝ) (hδ' : 0 < δ')
    (hδsmall : δ' ≤ 1 / 100) :
    onlineT3AllSuffixActualEpisodeArrayRadiusSet H K hH E fallback c₁ c₂ δ' ≤
      onlineT3AllSuffixActualEpisodeArrayExpandedRadiusSet H K hH E fallback c₁ c₂ δ' := by
  intro sample hsample j
  have hsource := hsample j
  change |onlineT3ActualSuffixEpisodeArray H K hH E sample.1 fallback sample.2 δ' c₁ c₂ j| ≤
      Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
        Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ') at hsource
  let L := Real.log (1 / δ')
  have hL : 2 ≤ L := onlineT3_sourceLog_ge_two δ' hδ' hδsmall
  have hT6 := onlineActualT6UCB_le_policy_difference H K hH E sample.1 fallback sample.2
    δ' c₁ c₂
  have hp : 0 ≤ onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ := by
    unfold onlineActualT6Policy
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.variance_nonneg _ _
  have hd : 0 ≤ onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ := by
    unfold onlineActualT6Difference
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.expectation_nonneg _ (fun _ => sq_nonneg _)
  have hu : 0 ≤ onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ := by
    unfold onlineActualT6UCB
    apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro k hk
    exact FiniteDistribution.variance_nonneg _ _
  have hroot :
      Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * L) ≤
        4 * Real.sqrt (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * L) +
        4 * Real.sqrt (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * L) := by
    exact onlineVarianceRadius_le_policy_difference
      (onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂)
      (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂)
      (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂)
      L hu hp hd (by linarith) hT6
  calc
    |onlineT3ActualSuffixEpisodeArray H K hH E sample.1 fallback sample.2 δ' c₁ c₂ j| ≤
        Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * L) +
          5 * (H : ℝ) * L := by simpa [L] using hsource
    _ ≤ 4 * Real.sqrt (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * L) +
          4 * Real.sqrt (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * L) +
          5 * (H : ℝ) * L := by
        calc
          _ = 5 * (H : ℝ) * L +
              Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * L) := by ring
          _ ≤ 5 * (H : ℝ) * L +
              (4 * Real.sqrt (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * L) +
                4 * Real.sqrt (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * L)) :=
            by simpa [add_comm, add_left_comm, add_assoc] using
              (add_le_add_right hroot (5 * (H : ℝ) * L))
          _ = _ := by ring

/-- All suffix starts obey the expanded source radius under the same actual
law, with the same confidence as the T₆-UCB event. -/
theorem onlineT3AllSuffixActualEpisodeArrayExpandedRadius_probability
    (H K : ℕ) (hH : 0 < H) (hN : 2 ≤ K * H)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (c₁ c₂ δ' : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hδ' : 0 < δ')
    (hδsmall : δ' ≤ 1 / 100) :
    1 - 2 * (H : ℝ) * (Nat.log2 (K * H) : ℝ) * δ' ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂) (K * H)).rowMeasure.real
        (onlineT3AllSuffixActualEpisodeArrayExpandedRadiusSet H K hH E fallback c₁ c₂ δ') := by
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
    (onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂) (K * H)).rowMeasure
  have hbase := onlineT3AllSuffixActualEpisodeArrayRadius_probability
    H K hH hN E ρ fallback c₁ c₂ δ' hc₁ hc₂ hδ' hδsmall
  have hsub :
      onlineT3AllSuffixActualEpisodeArrayRadiusSet H K hH E fallback c₁ c₂ δ' ≤
        onlineT3AllSuffixActualEpisodeArrayExpandedRadiusSet H K hH E fallback c₁ c₂ δ' :=
    onlineT3AllSuffixActualEpisodeArrayRadiusSet_subset_expanded
      H K hH E fallback c₁ c₂ δ' hδ' hδsmall
  have hmono := measure_mono (μ := μ) hsub
  have hreal := ENNReal.toReal_mono
    (measure_ne_top μ (onlineT3AllSuffixActualEpisodeArrayExpandedRadiusSet
      H K hH E fallback c₁ c₂ δ')) hmono
  change 1 - 2 * (H : ℝ) * (Nat.log2 (K * H) : ℝ) * δ' ≤ μ.real _
  exact hbase.trans hreal

end StatisticalRL.OnlineRL

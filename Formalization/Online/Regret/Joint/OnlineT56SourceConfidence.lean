import Formalization.Online.Regret.T3.OnlineT3SuffixExpandedFamily
import Formalization.Online.Regret.T0.OnlineT0ActualConfidence
import Formalization.Online.Regret.Joint.OnlineT56JointConditional
import Formalization.Online.Regret.Joint.OnlineT56SimplifiedConfidence
import Formalization.Online.SourceOptimism.SourceOptimismAllocation
import Formalization.Online.Regret.W1.OnlineUCBVISourceIota

/-! Unconditional same-law consumers of the canonical masked-T3 suffix family.
The source T3 event is derived from the absolute suffix event; T0 and T56
confidence are then obtained by applying their proved same-law consumers. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance finalT3State : MeasurableSpace State := ⊤
noncomputable local instance finalT3Sample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤
noncomputable local instance finalT3StateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance finalT3ActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The absolute canonical episode-array event implies the source one-sided
T3 suffix family; its summands are the same actual pre-episode capped rows. -/
theorem onlineT3ExpandedEpisodeArray_subset_T0SourceFamily
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) :
    onlineT3AllSuffixActualEpisodeArrayExpandedRadiusSet H K hH E fallback c₁ c₂ δ ≤
      onlineActualT0T3SuffixFamily H K hH E fallback δ c₁ c₂ := by
  intro sample hsample j
  have harray := hsample j
  have hle := le_abs_self
    (onlineT3ActualSuffixEpisodeArray H K hH E sample.1 fallback sample.2 δ c₁ c₂ j)
  have hbound := hle.trans harray
  change (∑ k : Fin K, ∑ n ∈ Finset.Ico j.val H,
      onlineCappedEpisodeT3 H
        (onlineT0ActualSuffixStage H K hH E sample.1 fallback sample.2 δ c₁ c₂ k)
        (onlineT0ActualSuffixState H K hH E sample.1 fallback sample.2 δ c₁ c₂ k)
        (onlineT0ActualSuffixAction H K hH E sample.1 fallback sample.2 δ c₁ c₂ k)
        (Real.log (1 / δ)) c₁ c₂ n) ≤ _
  simpa [onlineT3ActualSuffixEpisodeArray, onlineT3SuffixArrayStage,
    onlineT3SuffixArrayState, onlineT3SuffixArrayAction,
    onlineT0ActualSuffixStage, onlineT0ActualSuffixState, onlineT0ActualSuffixAction,
    onlineT4EpisodeState, onlineT4PlayedAction] using hbound

/-- The exact source T3 confidence bound under the actual sequential law,
with no supplied concentration premise. -/
theorem onlineT0SourceT3SuffixFamily_probability
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    1 - 2 * (H : ℝ) * (Nat.log2 (K * H) : ℝ) * δ ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) (K * H)).rowMeasure.real
        (onlineActualT0T3SuffixFamily H K hH E fallback δ c₁ c₂) := by
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
    (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) (K * H)).rowMeasure
  have hN : 2 ≤ K * H := hK.trans (Nat.le_mul_of_pos_right K hH)
  have hbase := onlineT3AllSuffixActualEpisodeArrayExpandedRadius_probability
    H K hH hN E ρ fallback c₁ c₂ δ (by linarith) (by nlinarith [sq_nonneg c₁])
      hδ hδsmall
  have hsubset := onlineT3ExpandedEpisodeArray_subset_T0SourceFamily H K hH E fallback δ c₁ c₂
  have hmono := measure_mono (μ := μ) hsubset
  have hreal := ENNReal.toReal_mono
    (measure_ne_top μ (onlineActualT0T3SuffixFamily H K hH E fallback δ c₁ c₂)) hmono
  change 1 - 2 * (H : ℝ) * (Nat.log2 (K * H) : ℝ) * δ ≤ μ.real _
  exact hbase.trans hreal

/-- The uniform source T0 optimism event has its actual-law 9M confidence
bound after discharging the T3 event probability internally. -/
theorem onlineT0_optimisticUniform_actual_confidence
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    1 - 9 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualT0OptimisticUniformEvent H K hH E fallback δ c₁ c₂) := by
  let hprob := onlineT0SourceT3SuffixFamily_probability H K hH hK E ρ fallback δ c₁ c₂
    hδ hδsmall hc₁ hc₂
  exact onlineT0_optimisticUniform_confidence_of_T3 H K hH hK E ρ fallback δ c₁ c₂
    hδ hδsmall hc₁ hc₂ hprob

/-- The actual first-14M T56 event follows unconditionally from the proved
T0 source confidence event, on the same reset/transition law. -/
theorem onlineT0_to_T56Joint_actual_confidence
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    1 - 14 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualT56JointEvent H K hH E fallback δ c₁ c₂) := by
  let hT0 := onlineT0_optimisticUniform_actual_confidence H K hH hK E ρ fallback δ c₁ c₂
    hδ hδsmall hc₁ hc₂
  exact onlineActualT56_joint_confidence_of_T0 H K hH hK E ρ fallback δ c₁ c₂
    hδ hδsmall hc₁ hc₂ hT0

/-- Fixed universal constants 4 and 16 meet the T2 iota threshold for the
source allocated confidence parameter. This wrapper only discharges that
scalar side condition; the source large-sample premise remains visible. -/
theorem onlineSourceT56Simplified_actual_confidence_fixed_constants
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hlarge :
      (Fintype.card State : ℝ) * Fintype.card Action * H^2 *
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K
          (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K) ≤ K) :
    let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) 4 16
    1 - 30 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualT56JointEvent H K hH E fallback δ' 4 16 ∩
         onlineActualT56SimplifiedEvent H K hH E fallback δ' 4 16) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  have hKpos : 0 < K := by omega
  have hdomain := onlineSourceOptimismDeltaPrime_domain δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδone Fintype.card_pos Fintype.card_pos hH hKpos
  have hI := onlineUCBVI_iota_meets_T2_constants (Fintype.card State)
    (Fintype.card Action) H K δ' Fintype.card_pos Fintype.card_pos hH hK hdomain.1 hdomain.2
  have hT0 := onlineT0_to_T56Joint_actual_confidence H K hH hK E ρ fallback δ' 4 16
    hdomain.1 hdomain.2 (by norm_num) (by norm_num)
  exact onlineSourceAllocated_actualT56Complete_of_joint H K hH hK E ρ fallback δ 4 16
    hδ hδone (by norm_num) (by norm_num) hI hlarge hT0

/-! Source-allocated confidence closure with constants fixed to 4 and 16
before the finite MDP parameters. -/
theorem onlineSourceAllocated_T3_T56_simplified_actual_confidence
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) 4 16
    (1 - 14 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualT56JointEvent H K hH E fallback δ' 4 16)) ∧
    ((Fintype.card State : ℝ) * Fintype.card Action * H^2 *
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ' ≤ K →
      1 - 30 * (Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H^2 * K * δ' <
        (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
          (onlineActualT56JointEvent H K hH E fallback δ' 4 16 ∩
           onlineActualT56SimplifiedEvent H K hH E fallback δ' 4 16)) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  have hKpos : 0 < K := by omega
  have hdomain := onlineSourceOptimismDeltaPrime_domain δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδone Fintype.card_pos Fintype.card_pos hH hKpos
  have hfirst := onlineT0_to_T56Joint_actual_confidence H K hH hK E ρ fallback δ' 4 16
    hdomain.1 hdomain.2 (by norm_num) (by norm_num)
  have hsecond := onlineSourceT56Simplified_actual_confidence_fixed_constants
    H K hH hK E ρ fallback δ hδ hδone
  refine ⟨?_, ?_⟩
  · simpa only [δ'] using hfirst
  · intro hlarge
    simpa only [δ'] using hsecond hlarge

end StatisticalRL.OnlineRL

import Formalization.Online.QLearning.ActualEpisode
import Formalization.Online.SourceOptimism.StackSequentialLawEquality

/-! Specialization of the proved reset/transcript law to
 the chronological Q-learning planner. Not yet compiler checked. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qLearningLawStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance qLearningLawStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance qLearningLawActionDecidable : DecidableEq Action := Classical.decEq Action
local instance qLearningLawTranscriptMeasurable (H K : ℕ) :
    MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤
local instance qLearningLawAtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

/-- Actual Q-learning resets and complete observed transcripts have the same
law in the independent-row-stack and sequential experiments. -/
theorem qLearning_stack_sequential_transcriptLaw_eq
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (bonus : ℕ → ℝ) :
    (onlineMDPInitialStackLaw E ρ K).map
      (fun sample => (sample.1, onlineStackHistory
        (onlineEpisodicChoose H K hH sample.1 fallback (qLearningActualEpisodePlanner hH E bonus))
        (onlineFiniteStackExtend K fallback sample.2) (K*H))) =
    (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure.map
      (fun sample => (sample.1, qLearningActualSequentialHistory hH E bonus sample.1 fallback sample.2)) := by
  simpa only [qLearningActualSequentialHistory] using
    onlineStack_sequential_transcriptLaw_eq H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H) le_rfl

/-- Any event of the actual reset vector and complete observed transcript has
the same probability in the two experiments. -/
theorem qLearning_stack_sequential_transcriptEvent_real_eq
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (bonus : ℕ → ℝ)
    (target : Set (OnlineResetTranscript State Action H K)) :
    (onlineMDPInitialStackLaw E ρ K).real
      {sample | (sample.1, onlineStackHistory
        (onlineEpisodicChoose H K hH sample.1 fallback (qLearningActualEpisodePlanner hH E bonus))
        (onlineFiniteStackExtend K fallback sample.2) (K*H)) ∈ target} =
    (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure.real
      {sample | (sample.1, qLearningActualSequentialHistory hH E bonus sample.1 fallback sample.2) ∈ target} := by
  classical
  have h := qLearning_stack_sequential_transcriptLaw_eq H K hH E ρ fallback bonus
  have heq := congrArg (fun law : Measure (OnlineResetTranscript State Action H K) => law.real target) h
  simpa only [measureReal_def, Measure.map_apply (measurable_of_countable _)
    ((Set.to_countable target).measurableSet)] using heq
end StatisticalRL.OnlineRL

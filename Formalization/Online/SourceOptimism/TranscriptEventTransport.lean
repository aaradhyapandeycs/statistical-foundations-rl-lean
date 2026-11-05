import Formalization.Online.SourceOptimism.StackSequentialLawEquality

/-! generic event consequence of the proved reset/transcript law
identity. No coupling, independence or random-index premise is added. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance decouplingEventStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance decouplingEventStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance decouplingEventActionDecidable : DecidableEq Action := Classical.decEq Action
local instance decouplingEventTranscriptMeasurable (H K : ℕ) :
    MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤
local instance decouplingEventAtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

theorem onlineStack_sequential_transcriptEvent_real_eq
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n : ℕ) (hn : n≤K*H)
    (target : Set (OnlineResetTranscript State Action H K)) :
    (onlineMDPInitialStackLaw E ρ K).real
      {sample | (sample.1,onlineStackHistory
        (onlineEpisodicChoose H K hH sample.1 fallback planner)
        (onlineFiniteStackExtend K fallback sample.2) n) ∈ target} =
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner n).rowMeasure.real
      {sample | (sample.1,onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH sample.1 fallback planner) n [] sample.2) ∈ target} := by
  classical
  have hcouple := onlineStack_sequential_transcriptLaw_eq H K hH E ρ fallback planner n hn
  have heq := congrArg (fun law : Measure (OnlineResetTranscript State Action H K) =>
    law.real target) hcouple
  simpa only [measureReal_def,Measure.map_apply (measurable_of_countable _)
    ((Set.to_countable target).measurableSet)] using heq

end StatisticalRL.OnlineRL

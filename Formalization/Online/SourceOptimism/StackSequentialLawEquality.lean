import Formalization.Online.SourceOptimism.RealizedPathAtom
import Formalization.Online.SourceOptimism.FiniteAtomLawComparison

/-! Full reset/transcript pushforward equality
from actual atom calculations. Source correspondence and the scope of the equality require independent review. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineLawEqualityStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

abbrev OnlineResetTranscript (State Action : Type*) (H K : ℕ) :=
  (Fin K → State) × List (OnlineMDPRow State Action H × State)
local instance onlineLawEqualityTranscriptMeasurable (H K : ℕ) :
    MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤

local instance onlineSequentialAtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

/-- The independent-reset stack experiment and independently normalized direct
sequential experiment have exactly the same full observed history law through
any n≤KH. No conditional-on-random-count iid or coupling premise is required. -/
theorem onlineStack_sequential_transcriptLaw_eq
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n : ℕ) (hn : n≤K*H) :
    (onlineMDPInitialStackLaw E ρ K).map
      (fun sample => (sample.1,onlineStackHistory
        (onlineEpisodicChoose H K hH sample.1 fallback planner)
        (onlineFiniteStackExtend K fallback sample.2) n)) =
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner n).rowMeasure.map
      (fun sample => (sample.1,onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH sample.1 fallback planner) n [] sample.2)) := by
  let μ := onlineMDPInitialStackLaw E ρ K
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner n
  let observe := fun sample : (Fin K → State) × (OnlineMDPRow State Action H × Fin K → State) =>
    (sample.1,onlineStackHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
      (onlineFiniteStackExtend K fallback sample.2) n)
  let encode := fun sample : (Fin K → State) × OnlineOutcomePath State n =>
    (sample.1,onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) n [] sample.2)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ,onlineMDPInitialStackLaw,onlineMDPStackLaw]
    infer_instance
  have hinj : Function.Injective encode :=
    onlineRealizedPath_reset_transcript_injective H K hH fallback planner n
  have hatom (sample : (Fin K → State) × OnlineOutcomePath State n) :
      μ {data | observe data=encode sample}=ENNReal.ofReal (ν.prob sample) := by
    rcases sample with ⟨initial,path⟩
    have h := onlineRealizedPath_stack_atom H K hH E ρ initial fallback planner n hn path
    simpa [μ,ν,observe,encode,Prod.mk.injEq] using h
  exact (onlineFiniteAtom_law_comparison μ ν observe encode hinj hatom).2

end StatisticalRL.OnlineRL

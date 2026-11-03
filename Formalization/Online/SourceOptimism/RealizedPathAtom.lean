import Formalization.Online.SourceOptimism.StackSequentialAtomComparison
import Formalization.Online.SourceOptimism.SequentialTranscriptUniqueness

/-! Consistency and row enumeration are derived
for every realized direct sequential path; source path-law equality is unclaimed. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineRealizedAtomStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- Each direct sequential reset/path atom equals the stack mass of its actual
reconstructed transcript. No transcript consistency, row enumeration, desired
law identity or random-count independence is left as an input. -/
theorem onlineRealizedPath_stack_atom
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (n : ℕ) (hn : n≤K*H) (path : OnlineOutcomePath State n) :
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) n [] path
    onlineMDPInitialStackLaw E ρ K
      {sample | sample.1=initial ∧
        onlineStackHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
          (onlineFiniteStackExtend K fallback sample.2) n=history} =
      ENNReal.ofReal ((onlineSequentialEpisodeLaw H K hH E ρ fallback planner n).prob
        (initial,path)) := by
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose n [] path
  have hlen : history.length=n := by
    simpa [history] using onlineSequentialPathHistory_length choose n [] path
  have hempty : onlineTranscriptRowsConsistent choose [] := by
    intro j
    exact Fin.elim0 j
  have hr : onlineTranscriptRowsConsistent choose history :=
    onlineSequentialPathHistory_rows_consistent choose n [] hempty path
  let rowAt := onlineTranscriptRowSequence (choose []) history
  have hrows (j : Fin history.length) : rowAt j.val=(history.get j).1 :=
    onlineTranscriptRowSequence_agrees (choose []) history j
  have h := onlineStack_sequential_atom_comparison H K hH E ρ initial fallback
    planner n path history rfl (by simpa only [hlen] using hn) hr rowAt hrows
  simpa only [hlen] using h

/-- The common reset/transcript representation is injective on direct path
atoms, so a future pushforward comparison does not merge distinct paths. -/
theorem onlineRealizedPath_reset_transcript_injective
    (H K : ℕ) (hH : 0<H) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n : ℕ) :
    Function.Injective (fun sample : (Fin K → State) × OnlineOutcomePath State n =>
      (sample.1,onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH sample.1 fallback planner) n [] sample.2)) := by
  intro sample sample' heq
  rcases sample with ⟨initial,path⟩
  rcases sample' with ⟨initial',path'⟩
  have hi := congrArg Prod.fst heq
  change initial=initial' at hi
  subst initial'
  have hh := congrArg Prod.snd heq
  have hp := onlineSequentialPathHistory_injective
    (onlineEpisodicChoose H K hH initial fallback planner) n [] hh
  change path = path' at hp
  subst path'
  rfl

end StatisticalRL.OnlineRL

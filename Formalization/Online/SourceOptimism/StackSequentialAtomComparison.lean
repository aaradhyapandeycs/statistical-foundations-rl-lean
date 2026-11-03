import Formalization.Online.SourceOptimism.ResetHistoryAtom
import Formalization.Online.SourceOptimism.SequentialHistoryDensity
import Mathlib.Data.ENNReal.BigOperators

/-! Exact comparison of a compatible stack
reset/history atom and the direct sequential reset/path atom. Whole pushforward
law equality still needs deterministic path/history consistency and injectivity. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineAtomCompareStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- Both independently defined experiments have the same atom mass whenever
the direct path and fixed transcript are identified. No path-law equality or
random-count conditional independence is a premise. -/
theorem onlineStack_sequential_atom_comparison
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (n : ℕ) (path : OnlineOutcomePath State n)
    (history : List (OnlineMDPRow State Action H × State))
    (hpath : onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) n [] path=history)
    (hlen : history.length≤K*H)
    (hr : onlineTranscriptRowsConsistent
      (onlineEpisodicChoose H K hH initial fallback planner) history)
    (rowAt : ℕ → OnlineMDPRow State Action H)
    (hrows : ∀ j : Fin history.length, rowAt j.val=(history.get j).1) :
    onlineMDPInitialStackLaw E ρ K
      {sample | sample.1=initial ∧
        onlineStackHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
          (onlineFiniteStackExtend K fallback sample.2) history.length=history} =
      ENNReal.ofReal ((onlineSequentialEpisodeLaw H K hH E ρ fallback planner n).prob
        (initial,path)) := by
  rw [onlineResetHistory_atom H K hH E ρ initial fallback planner history hlen hr rowAt hrows]
  have hp := onlineSequentialOutcomeLaw_prob_eq_transcriptMass (onlineMDPSuccessorRowLaw E)
    (onlineEpisodicChoose H K hH initial fallback planner) n path
  rw [hpath,onlineTranscriptTransitionMass_eq_prod] at hp
  change _ = ENNReal.ofReal ((onlineInitialVectorLaw ρ K).prob initial *
    (onlineSequentialOutcomeLaw (onlineMDPSuccessorRowLaw E)
      (onlineEpisodicChoose H K hH initial fallback planner) n []).prob path)
  rw [hp,ENNReal.ofReal_mul ((onlineInitialVectorLaw ρ K).prob_nonneg initial)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ =>
    (onlineMDPSuccessorRowLaw E (history.get j).1).prob_nonneg (history.get j).2)]
  congr 1
  change (∏ k,ENNReal.ofReal (ρ.prob (initial k))) =
    ENNReal.ofReal (∏ k,ρ.prob (initial k))
  exact (ENNReal.ofReal_prod_of_nonneg (fun k _ => ρ.prob_nonneg (initial k))).symm

end StatisticalRL.OnlineRL

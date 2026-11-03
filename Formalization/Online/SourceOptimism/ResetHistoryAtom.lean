import Formalization.Online.SourceOptimism.EpisodicHistoryMass
import Formalization.Online.SourceOptimism.SequentialEpisodeLaw
import Mathlib.MeasureTheory.Measure.Prod

/-! Independent reset-vector integration of
stack history atoms. Direct sequential history atom comparison remains separate. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineResetAtomStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- The actual iid reset-vector measure assigns precisely its probability-
product mass, including impossible zero-mass reset vectors. -/
theorem onlineInitialVector_atom (ρ : FiniteDistribution State) (K : ℕ)
    (initial : Fin K → State) :
    Measure.pi (fun _ : Fin K => ρ.rowMeasure) {initial} =
      ∏ k,ENNReal.ofReal (ρ.prob (initial k)) := by
  rw [Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro k _
  rw [FiniteDistribution.rowMeasure,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rfl

/-- The joint reset/stack experiment gives a fixed reset vector and consistent
adaptive history their exact source reset-times-transition product mass. -/
theorem onlineResetHistory_atom
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (history : List (OnlineMDPRow State Action H × State))
    (hlen : history.length≤K*H)
    (hr : onlineTranscriptRowsConsistent
      (onlineEpisodicChoose H K hH initial fallback planner) history)
    (rowAt : ℕ → OnlineMDPRow State Action H)
    (hrows : ∀ j : Fin history.length, rowAt j.val=(history.get j).1) :
    onlineMDPInitialStackLaw E ρ K
      {sample | sample.1=initial ∧
        onlineStackHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
          (onlineFiniteStackExtend K fallback sample.2) history.length=history} =
      (∏ k,ENNReal.ofReal (ρ.prob (initial k))) *
        ∏ j : Fin history.length,
          ENNReal.ofReal (((E (history.get j).1.1).transition
            (history.get j).1.2.1 (history.get j).1.2.2).prob (history.get j).2) := by
  have hset : {sample : (Fin K → State) × (OnlineMDPRow State Action H × Fin K → State) |
      sample.1=initial ∧
        onlineStackHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
          (onlineFiniteStackExtend K fallback sample.2) history.length=history} =
      ({initial} ×ˢ {data | onlineStackHistory
        (onlineEpisodicChoose H K hH initial fallback planner)
        (onlineFiniteStackExtend K fallback data) history.length=history}) := by
    ext sample
    simp only [Set.mem_setOf_eq,Set.mem_prod,Set.mem_singleton_iff]
    constructor
    · rintro ⟨hi,hh⟩
      refine ⟨hi,?_⟩
      simpa only [hi] using hh
    · rintro ⟨hi,hh⟩
      refine ⟨hi,?_⟩
      simpa only [hi] using hh
  rw [hset,onlineMDPInitialStackLaw,Measure.prod_prod,onlineInitialVector_atom,
    onlineEpisodicHistory_stack_mass H K hH E initial fallback planner history
      hlen hr rowAt hrows]

end StatisticalRL.OnlineRL

import Formalization.Online.SourceOptimism.EpisodicStackSelector
import Formalization.Online.SourceOptimism.ChronologicalStageStackCap
import Formalization.Online.SourceOptimism.AdaptiveHistorySlotMass

/-! Actual stage/reset selector and K-slot
transition-product history masses, conditional on fixed episode-reset values.
Equality to the source online trajectory measure is a separate obligation. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineEpisodicMassStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- The predictable episodic selector forces each record's stage tag to be
its chronological index mod H, even for an outcome-dependent planner. -/
theorem onlineEpisodicTranscript_stage
    (H K : ℕ) (hH : 0<H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (history : List (OnlineMDPRow State Action H × State))
    (hr : onlineTranscriptRowsConsistent
      (onlineEpisodicChoose H K hH initial fallback planner) history)
    (rowAt : ℕ → OnlineMDPRow State Action H)
    (hrows : ∀ j : Fin history.length, rowAt j.val=(history.get j).1)
    (j : Fin history.length) : (rowAt j.val).1.val=j.val%H := by
  rw [hrows j,hr j,onlineEpisodicChoose_stage]
  simp [List.length_take,Nat.min_eq_left j.isLt.le]

/-- Stage consistency derives the per-row slot bound internally. Hence the
KH-step actual selector uses only K successor samples for each (h,s,a). -/
theorem onlineEpisodicHistory_stack_mass
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (history : List (OnlineMDPRow State Action H × State))
    (hlen : history.length≤K*H)
    (hr : onlineTranscriptRowsConsistent
      (onlineEpisodicChoose H K hH initial fallback planner) history)
    (rowAt : ℕ → OnlineMDPRow State Action H)
    (hrows : ∀ j : Fin history.length, rowAt j.val=(history.get j).1) :
    onlineMDPStackLaw E K
      {data | onlineStackHistory (onlineEpisodicChoose H K hH initial fallback planner)
        (onlineFiniteStackExtend K fallback data) history.length=history} =
      ∏ j : Fin history.length,
        ENNReal.ofReal (((E (history.get j).1.1).transition
          (history.get j).1.2.1 (history.get j).1.2.2).prob (history.get j).2) := by
  have hslots (j : Fin history.length) :
      onlineVisitCount rowAt j.val (rowAt j.val)<K := by
    apply onlineChronologicalStageCount_lt_K rowAt K j.val hH
      (j.isLt.trans_le hlen) (rowAt j.val)
    · intro k hk
      exact onlineEpisodicTranscript_stage H K hH initial fallback planner history hr
        rowAt hrows ⟨k,hk.trans j.isLt⟩
    · exact onlineEpisodicTranscript_stage H K hH initial fallback planner history hr
        rowAt hrows j
  exact onlineAdaptiveHistory_mass_of_slot_bound (onlineMDPSuccessorRowLaw E)
    (onlineEpisodicChoose H K hH initial fallback planner) K fallback history hr
    rowAt hrows hslots

end StatisticalRL.OnlineRL

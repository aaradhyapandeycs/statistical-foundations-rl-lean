import Formalization.Online.SourceOptimism.AdaptiveHistoryMass

/-! Finite slot bounds replace the crude
chronological-length bound; allows KH steps with K slots per stage-tagged row. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Row Outcome : Type*} [Fintype Row] [DecidableEq Row] [Fintype Outcome]
local instance onlineSlotHistoryOutcomeMeasurable : MeasurableSpace Outcome := ⊤

noncomputable def onlineVisitSlotCoordinate
    (rowAt : ℕ → Row) (K n : ℕ)
    (hslots : ∀ j : Fin n, onlineVisitCount rowAt j.val (rowAt j.val)<K)
    (j : Fin n) : Row × Fin K :=
  (rowAt j.val,⟨onlineVisitCount rowAt j.val (rowAt j.val),hslots j⟩)

theorem onlineVisitSlotCoordinate_injective
    (rowAt : ℕ → Row) (K n : ℕ)
    (hslots : ∀ j : Fin n, onlineVisitCount rowAt j.val (rowAt j.val)<K) :
    Function.Injective (onlineVisitSlotCoordinate rowAt K n hslots) := by
  intro j k heq
  apply onlineVisitCoordinate_injective rowAt n
  exact congrArg (fun p : Row × Fin K => (p.1,p.2.val)) heq

/-- The slot bound is an algorithmic index fact, not a stochastic conclusion.
The chronological transcript can have more than K records. -/
theorem onlineAdaptiveHistory_mass_of_slot_bound
    (d : Row → FiniteDistribution Outcome)
    (choose : List (Row × Outcome) → Row) (K : ℕ) (fallback : Outcome)
    (history : List (Row × Outcome))
    (hr : onlineTranscriptRowsConsistent choose history) (rowAt : ℕ → Row)
    (hrows : ∀ j : Fin history.length, rowAt j.val=(history.get j).1)
    (hslots : ∀ j : Fin history.length,
      onlineVisitCount rowAt j.val (rowAt j.val)<K) :
    onlineStackProductLaw (fun i : Row × Fin K => d i.1)
      {data | onlineStackHistory choose (onlineFiniteStackExtend K fallback data)
        history.length=history} =
      ∏ j : Fin history.length, ENNReal.ofReal ((d (history.get j).1).prob (history.get j).2) := by
  have hset : {data : Row × Fin K → Outcome |
      onlineStackHistory choose (onlineFiniteStackExtend K fallback data)
        history.length=history} =
      {data | ∀ j : Fin history.length,
        data (onlineVisitSlotCoordinate rowAt K history.length hslots j)=(history.get j).2} := by
    ext data
    rw [Set.mem_setOf_eq,onlineStackHistory_eq_iff_transcriptSteps,
      onlineTranscriptSteps_iff_rows_and_coordinates]
    simp only [hr,true_and,Set.mem_setOf_eq]
    have heq (j : Fin history.length) :
        onlineFiniteStackExtend K fallback data (history.get j).1
          (onlineRowOutcomes (history.take j.val) (history.get j).1).length =
        data (onlineVisitSlotCoordinate rowAt K history.length hslots j) := by
      rw [onlineTranscript_rowCount_eq_visitCount history rowAt hrows j.val j.isLt.le
        (history.get j).1,← hrows j]
      simp [onlineFiniteStackExtend,onlineVisitSlotCoordinate,hslots j]
    simp_rw [heq]
  rw [hset,onlineDistinctCylinder_mass (fun i : Row × Fin K => d i.1)
    history.length (onlineVisitSlotCoordinate rowAt K history.length hslots)
    (onlineVisitSlotCoordinate_injective rowAt K history.length hslots)
    (fun j => (history.get j).2)]
  apply Finset.prod_congr rfl
  intro j _
  rw [show (onlineVisitSlotCoordinate rowAt K history.length hslots j).1=rowAt j.val from rfl,
    hrows j]

end StatisticalRL.OnlineRL

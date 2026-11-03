import Formalization.Online.SourceOptimism.StackRunCylinderIdentity
import Formalization.Online.SourceOptimism.VisitTranscriptMass

/-! actual adaptive stack run-history masses.
The separate source online trajectory selector/path law is not assumed equal. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Row Outcome : Type*} [Fintype Row] [DecidableEq Row] [Fintype Outcome]
local instance onlineAdaptiveHistoryOutcomeMeasurable : MeasurableSpace Outcome := ⊤

/-- Total extension of a finite successor array. The arbitrary fallback is
never read by the bounded transcript event below. -/
def onlineFiniteStackExtend (K : ℕ) (fallback : Outcome)
    (data : Row × Fin K → Outcome) (r : Row) (n : ℕ) : Outcome :=
  if hn : n<K then data (r,⟨n,hn⟩) else fallback

/-- A consistent fixed history is exactly its finite distinct-coordinate
cylinder in the actual product array. Selection remains history dependent. -/
theorem onlineAdaptiveHistory_event_eq_cylinder
    (choose : List (Row × Outcome) → Row) (K : ℕ) (fallback : Outcome)
    (history : List (Row × Outcome)) (hlen : history.length≤K)
    (hr : onlineTranscriptRowsConsistent choose history)
    (rowAt : ℕ → Row)
    (hrows : ∀ j : Fin history.length, rowAt j.val=(history.get j).1) :
    {data : Row × Fin K → Outcome |
      onlineStackHistory choose (onlineFiniteStackExtend K fallback data) history.length=history} =
    {data | ∀ j : Fin history.length,
      data (onlineVisitCoordinateFin rowAt K history.length hlen j)=(history.get j).2} := by
  ext data
  rw [Set.mem_setOf_eq,onlineStackHistory_eq_iff_transcriptSteps,
    onlineTranscriptSteps_iff_rows_and_coordinates]
  simp only [hr,true_and,Set.mem_setOf_eq]
  have heq (j : Fin history.length) :
      onlineFiniteStackExtend K fallback data (history.get j).1
        (onlineRowOutcomes (history.take j.val) (history.get j).1).length =
      data (onlineVisitCoordinateFin rowAt K history.length hlen j) := by
    have hc := onlineTranscript_rowCount_eq_visitCount history rowAt hrows
      j.val j.isLt.le (history.get j).1
    rw [hc,← hrows j]
    have hbound : onlineVisitCount rowAt j.val (rowAt j.val)<K :=
      (onlineVisitCoordinateFin rowAt K history.length hlen j).2.isLt
    simp [onlineFiniteStackExtend,onlineVisitCoordinateFin,hbound]
  simp_rw [heq]

/-- The finite adaptive run assigns the exact transition-product mass to each
consistent fixed history. No conditioning on its probability or random count
is used; zero-probability histories are handled by the same equality. -/
theorem onlineAdaptiveHistory_mass
    (d : Row → FiniteDistribution Outcome)
    (choose : List (Row × Outcome) → Row) (K : ℕ) (fallback : Outcome)
    (history : List (Row × Outcome)) (hlen : history.length≤K)
    (hr : onlineTranscriptRowsConsistent choose history)
    (rowAt : ℕ → Row)
    (hrows : ∀ j : Fin history.length, rowAt j.val=(history.get j).1) :
    onlineStackProductLaw (fun i : Row × Fin K => d i.1)
      {data | onlineStackHistory choose (onlineFiniteStackExtend K fallback data)
        history.length=history} =
      ∏ j : Fin history.length, ENNReal.ofReal ((d (history.get j).1).prob (history.get j).2) := by
  rw [onlineAdaptiveHistory_event_eq_cylinder choose K fallback history hlen hr rowAt hrows,
    onlineVisitTranscript_cylinder_mass d rowAt K history.length hlen
      (fun j => (history.get j).2)]
  apply Finset.prod_congr rfl
  intro j _
  rw [hrows j]

/-- Histories inconsistent with the predictable row selection have zero mass,
without adding a source restriction or dividing by a zero-probability event. -/
theorem onlineAdaptiveHistory_inconsistent_mass_zero
    (d : Row → FiniteDistribution Outcome)
    (choose : List (Row × Outcome) → Row) (K : ℕ) (fallback : Outcome)
    (history : List (Row × Outcome))
    (hr : ¬onlineTranscriptRowsConsistent choose history) :
    onlineStackProductLaw (fun i : Row × Fin K => d i.1)
      {data | onlineStackHistory choose (onlineFiniteStackExtend K fallback data)
        history.length=history} = 0 := by
  have hempty : {data : Row × Fin K → Outcome |
      onlineStackHistory choose (onlineFiniteStackExtend K fallback data)
        history.length=history} = ∅ := by
    ext data
    simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
    intro h
    exact hr ((onlineTranscriptSteps_iff_rows_and_coordinates choose _ history).mp
      ((onlineStackHistory_eq_iff_transcriptSteps choose _ history).mp h)).1
  rw [hempty,measure_empty]

end StatisticalRL.OnlineRL

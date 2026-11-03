import Formalization.Online.SourceOptimism.DistinctCylinderMass
import Formalization.Online.SourceOptimism.VisitCoordinateDistinct

/-! Product mass of a fixed visit transcript's
distinct stack constraints. Actual online trajectory-law identification remains
separate and no random-count conditional independence is assumed. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Row Outcome : Type*} [Fintype Row] [DecidableEq Row] [Fintype Outcome]
local instance onlineTranscriptOutcomeMeasurable : MeasurableSpace Outcome := ⊤

/-- The coordinate used by a fixed chronological visit fits in a finite stack
of size K, since its number of prior same-row visits is at most its index. -/
noncomputable def onlineVisitCoordinateFin
    (rowAt : ℕ → Row) (K n : ℕ) (hn : n≤K) (j : Fin n) : Row × Fin K := by
  classical
  letI : DecidableEq Row := Classical.decEq Row
  have hc : onlineVisitCount rowAt j.val (rowAt j.val) ≤ j.val := by
    unfold onlineVisitCount
    calc
      _ ≤ (Finset.range j.val).card := Finset.card_filter_le _ _
      _ = j.val := Finset.card_range _
  exact (rowAt j.val,⟨onlineVisitCount rowAt j.val (rowAt j.val),
    hc.trans_lt (j.isLt.trans_le hn)⟩)

theorem onlineVisitCoordinateFin_injective
    (rowAt : ℕ → Row) (K n : ℕ) (hn : n≤K) :
    Function.Injective (onlineVisitCoordinateFin rowAt K n hn) := by
  intro j k heq
  apply onlineVisitCoordinate_injective rowAt n
  have h := congrArg (fun p : Row × Fin K => (p.1,p.2.val)) heq
  exact h

/-- Every fixed visit transcript has the transition-product cylinder mass.
Adaptivity enters through the consistency/prefix identity in the separate
history construction, not an independence premise on the realized count. -/
theorem onlineVisitTranscript_cylinder_mass
    (d : Row → FiniteDistribution Outcome) (rowAt : ℕ → Row)
    (K n : ℕ) (hn : n≤K) (outcome : Fin n → Outcome) :
    onlineStackProductLaw (fun i : Row × Fin K => d i.1)
      {data | ∀ j, data (onlineVisitCoordinateFin rowAt K n hn j)=outcome j} =
      ∏ j, ENNReal.ofReal ((d (rowAt j.val)).prob (outcome j)) := by
  exact onlineDistinctCylinder_mass (fun i : Row × Fin K => d i.1) n
    (onlineVisitCoordinateFin rowAt K n hn)
    (onlineVisitCoordinateFin_injective rowAt K n hn) outcome

end StatisticalRL.OnlineRL

import Formalization.Probability.FiniteDistributionBridge
import Formalization.Probability.FiniteMarkov.Definitions
import Formalization.ModelFree.QLearningCountablePinskerProductionBridge
import Formalization.RobustRL.TVCore
import Formalization.RobustRL.TVEventBridge
import Formalization.RobustRL.LowerBounds.Ch7Definitions

/-!
# One total-variation vocabulary

The library carries several definitions of total variation (TV).  This module records, once, how
they are related.

## Mathlib status (pin `32d24245`)

Mathlib has no total-variation distance between probability measures or probability vectors
(there is no `tvDist`, `variationDist` or similar).  The only `totalVariation` is
`MeasureTheory.SignedMeasure.totalVariation`, the total-variation measure of a signed measure
built from its Jordan decomposition; no bridge from it to the half-L1 distance is provided here.
This is the recorded reason for keeping a local TV.

## The notions and their relationships

For finite vectors `p q : Ω → ℝ`:

* `FiniteMarkov.tvDist p q`, `QLearning.qFiniteTotalVariation p q` and (for a finite carrier)
  `QLearning.CountablePinsker.qCountableTotalVariation p q` are all the half-L1 distance
  `(1/2) * ∑ ω, |p ω - q ω|`.  The first two are definitionally equal; the countable one equals
  them by `tsum_fintype`.  No hypothesis is needed (no junk-value differences).
* `RobustRL.TVProof.Event.eventMassDifference` and `RobustRL.eventTVMassDifference` are the same
  signed event discrepancy, and `RobustRL.TVProof.Event.qFiniteEventTV` and `RobustRL.eventTV` are
  the same finite maximum of the absolute discrepancy over `Finset Ω`; both are definitionally
  equal.
* `RobustRL.Ch7.tvBall p σ` is the set of rows whose half-L1 distance to `p` is at most `σ`.
* Event-supremum TV versus half-L1 TV are **different formulas** that are equal exactly for
  probability vectors (nonnegative with sum one); this needs the hypotheses (without
  normalisation the half-L1 sum can exceed the event supremum).  The identity is
  `RobustRL.eventTV_eq_finiteTotalVariation`, and on the row measure of two finite distributions
  `tvDist_eq_iSup_abs_rowMeasure_real` states the standard characterisation
  `TV(P, Q) = ⨆ A measurable, |P(A) - Q(A)|`.
-/

open MeasureTheory
open scoped BigOperators

namespace StatisticalRL

section Identical

namespace FiniteMarkov

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- `FiniteMarkov.tvDist` is the half-L1 total variation `QLearning.qFiniteTotalVariation`
(definitional equality, no hypotheses). -/
theorem tvDist_eq_qFiniteTotalVariation (p q : X → ℝ) :
    tvDist p q = QLearning.qFiniteTotalVariation p q := rfl

end FiniteMarkov

namespace QLearning.CountablePinsker

/-- On a finite carrier the countable half-L1 total variation is the finite one (no hypotheses:
`tsum` over a finite type is the finite sum). -/
theorem qCountableTotalVariation_eq_qFiniteTotalVariation
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (p q : Ω → ℝ) :
    qCountableTotalVariation p q = QLearning.qFiniteTotalVariation p q := by
  rw [qCountableTotalVariation, QLearning.qFiniteTotalVariation, tsum_fintype]

end QLearning.CountablePinsker

namespace RobustRL

variable {State : Type*} [Fintype State] [DecidableEq State]

omit [Fintype State] [DecidableEq State] in
/-- The two copies of the signed event discrepancy coincide. -/
theorem eventTVMassDifference_eq_eventMassDifference (p q : State → ℝ) (A : Finset State) :
    eventTVMassDifference p q A = TVProof.Event.eventMassDifference p q A := rfl

omit [DecidableEq State] in
/-- The two copies of the finite event-supremum TV coincide. -/
theorem eventTV_eq_qFiniteEventTV (p q : State → ℝ) :
    eventTV p q = TVProof.Event.qFiniteEventTV p q := rfl

namespace Ch7

omit [DecidableEq State] in
/-- A row `q` lies in the TV ball of radius `σ` around `p` exactly when the half-L1 total
variation `FiniteMarkov.tvDist` of the two rows is at most `σ`. -/
theorem mem_tvBall_iff_tvDist_le (p : FiniteDistribution State) (σ : ℝ)
    (q : FiniteDistribution State) :
    q ∈ tvBall p σ ↔ FiniteMarkov.tvDist p.prob q.prob ≤ σ := Iff.rfl

end Ch7

end RobustRL

end Identical

section Event

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

local instance tvBridgeDiscrete : MeasurableSpace Ω := ⊤

/-- The real mass of an event under the row measure is the sum of the atom masses over the
event. -/
theorem rowMeasure_real_eq_sum_toFinset (d : FiniteDistribution Ω) (A : Set Ω) :
    d.rowMeasure.real A = ∑ x ∈ A.toFinite.toFinset, d.prob x := by
  haveI : IsProbabilityMeasure d.rowMeasure := isProbabilityMeasure_rowMeasure_top d
  haveI : DiscreteMeasurableSpace Ω := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have h := sum_measureReal_singleton (μ := d.rowMeasure) A.toFinite.toFinset
  rw [Set.Finite.coe_toFinset] at h
  rw [← h]
  exact Finset.sum_congr rfl fun x _ ↦ rowMeasure_real_singleton d x

/-- Total variation as a supremum over events.  For two finite distributions the half-L1 distance
`FiniteMarkov.tvDist` equals `⨆ A measurable, |P(A) - Q(A)|` for the row measures (the sigma-algebra
is the discrete one used by `rowMeasure`), the standard characterisation of total variation.  It
is the form in which Chapter 1 states total variation. -/
theorem tvDist_eq_iSup_abs_rowMeasure_real (P Q : FiniteDistribution Ω) :
    FiniteMarkov.tvDist P.prob Q.prob =
      ⨆ A : {A : Set Ω // MeasurableSet A},
        |P.rowMeasure.real A.1 - Q.rowMeasure.real A.1| := by
  classical
  obtain ⟨hbound, E, hE⟩ := RobustRL.eventTV_isMaximum P.prob Q.prob P.prob_nonneg
    Q.prob_nonneg P.sum_prob Q.sum_prob
  have hev (A : Set Ω) :
      |P.rowMeasure.real A - Q.rowMeasure.real A| =
        |RobustRL.eventTVMassDifference P.prob Q.prob A.toFinite.toFinset| := by
    rw [rowMeasure_real_eq_sum_toFinset, rowMeasure_real_eq_sum_toFinset]
    rfl
  have hbdd : BddAbove (Set.range fun A : {A : Set Ω // MeasurableSet A} ↦
      |P.rowMeasure.real A.1 - Q.rowMeasure.real A.1|) :=
    ⟨FiniteMarkov.tvDist P.prob Q.prob, by
      rintro _ ⟨A, rfl⟩
      exact (hev A.1).trans_le (hbound _)⟩
  apply le_antisymm
  · have hEset : |P.rowMeasure.real (E : Set Ω) - Q.rowMeasure.real (E : Set Ω)| =
        FiniteMarkov.tvDist P.prob Q.prob := by
      rw [hev]
      have : (E : Set Ω).toFinite.toFinset = E := by ext; simp
      rw [this]
      exact hE
    rw [← hEset]
    exact le_ciSup hbdd (⟨(E : Set Ω), MeasurableSpace.measurableSet_top⟩ :
      {A : Set Ω // MeasurableSet A})
  · refine ciSup_le fun A ↦ ?_
    exact (hev A.1).trans_le (hbound _)

end FiniteDistribution

end Event

end StatisticalRL

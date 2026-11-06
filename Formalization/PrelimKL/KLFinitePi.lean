import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Formalization.PrelimKL.KLMeasurableEquiv

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatisticalRL.PrelimKL

/-- KL tensorization for a finite dependent Pi family, by induction on the number of coordinates. -/
theorem klDiv_pi_fin
    (n : ℕ) (α : Fin n → Type*) [∀ i, MeasurableSpace (α i)]
    (P Q : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)] :
    InformationTheory.klDiv (Measure.pi P) (Measure.pi Q) =
      ∑ i, InformationTheory.klDiv (P i) (Q i) := by
  induction n with
  | zero =>
      rw [Measure.pi_of_empty P, Measure.pi_of_empty Q]
      simp
  | succ n ih =>
      let e : (∀ i : Fin (n + 1), α i) ≃ᵐ
          α 0 × (∀ j : Fin n, α j.succ) := MeasurableEquiv.piFinSuccAbove α 0
      let Ptail : ∀ j : Fin n, Measure (α j.succ) := fun j => P j.succ
      let Qtail : ∀ j : Fin n, Measure (α j.succ) := fun j => Q j.succ
      have hP : MeasurePreserving e (Measure.pi P) ((P 0).prod (Measure.pi Ptail)) :=
        measurePreserving_piFinSuccAbove P 0
      have hQ : MeasurePreserving e (Measure.pi Q) ((Q 0).prod (Measure.pi Qtail)) :=
        measurePreserving_piFinSuccAbove Q 0
      calc
        InformationTheory.klDiv (Measure.pi P) (Measure.pi Q) =
            InformationTheory.klDiv ((P 0).prod (Measure.pi Ptail))
              ((Q 0).prod (Measure.pi Qtail)) :=
          klDiv_measurePreserving_measurableEquiv e (Measure.pi P)
            ((P 0).prod (Measure.pi Ptail)) (Measure.pi Q)
            ((Q 0).prod (Measure.pi Qtail)) hP hQ
        _ = InformationTheory.klDiv (P 0) (Q 0) +
            InformationTheory.klDiv (Measure.pi Ptail) (Measure.pi Qtail) :=
          binary_product_klDiv_add (P 0) (Q 0) (Measure.pi Ptail) (Measure.pi Qtail)
        _ = ∑ i : Fin (n + 1), InformationTheory.klDiv (P i) (Q i) := by
          rw [Fin.sum_univ_succ]
          congr 1
          exact ih (fun j => α j.succ) Ptail Qtail

end StatisticalRL.PrelimKL

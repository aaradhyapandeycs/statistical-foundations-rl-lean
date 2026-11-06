import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Formalization.PrelimKL.KLFinitePi

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

namespace StatisticalRL.PrelimKL

/-- KL tensorization for any finite dependent product, reduced to the `Fin n` induction. -/
theorem klDiv_pi_eq_sum
    {ι : Type*} [Fintype ι]
    (α : ι → Type u) [∀ i, MeasurableSpace (α i)]
    (P Q : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)] :
    InformationTheory.klDiv (Measure.pi P) (Measure.pi Q) =
      ∑ i, InformationTheory.klDiv (P i) (Q i) := by
  let n := Fintype.card ι
  let e : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let αfin : Fin n → Type u := fun j => α (e j)
  let Pfin : ∀ j, Measure (αfin j) := fun j => P (e j)
  let Qfin : ∀ j, Measure (αfin j) := fun j => Q (e j)
  let E : (∀ i, α i) ≃ᵐ (∀ j, αfin j) :=
    (MeasurableEquiv.piCongrLeft α e).symm
  have hP : MeasurePreserving E (Measure.pi P) (Measure.pi Pfin) :=
    MeasurePreserving.symm (MeasurableEquiv.piCongrLeft α e)
      (measurePreserving_piCongrLeft P e)
  have hQ : MeasurePreserving E (Measure.pi Q) (Measure.pi Qfin) :=
    MeasurePreserving.symm (MeasurableEquiv.piCongrLeft α e)
      (measurePreserving_piCongrLeft Q e)
  calc
    InformationTheory.klDiv (Measure.pi P) (Measure.pi Q) =
        InformationTheory.klDiv (Measure.pi Pfin) (Measure.pi Qfin) :=
      klDiv_measurePreserving_measurableEquiv E (Measure.pi P) (Measure.pi Pfin)
        (Measure.pi Q) (Measure.pi Qfin) hP hQ
    _ = ∑ j : Fin n, InformationTheory.klDiv (Pfin j) (Qfin j) :=
      klDiv_pi_fin n αfin Pfin Qfin
    _ = ∑ i, InformationTheory.klDiv (P i) (Q i) := by
      simpa only [Pfin, Qfin] using
        (Equiv.sum_comp e (fun i => InformationTheory.klDiv (P i) (Q i)))

end StatisticalRL.PrelimKL

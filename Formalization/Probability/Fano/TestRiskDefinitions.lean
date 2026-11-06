import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Canonical Chapter 2 Fano testing foundations. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace StatisticalRL.PrelimFano

section Testing

variable {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
  [Fintype I] [Nonempty I] [MeasurableSingletonClass I]

/-- The source's tests, with measurability made explicit. -/
abbrev MeasurableTest := {ψ : Ω → I // Measurable ψ}

/-- Error probability for one hypothesis and one actual measurable test. -/
noncomputable def testError (P : I → Measure Ω)
    (ψ : MeasurableTest (Ω := Ω) (I := I)) (i : I) : ℝ :=
  (P i).real {x | ψ.1 x ≠ i}

/-- Average error of a single common test, with the source denominator `|I|`. -/
noncomputable def averageTestError (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)]
    (ψ : MeasurableTest (Ω := Ω) (I := I)) : ℝ :=
  (∑ i : I, testError P ψ i) / Fintype.card I

/-- Worst-hypothesis error of a single common test. -/
noncomputable def worstTestError (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)]
    (ψ : MeasurableTest (Ω := Ω) (I := I)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (testError P ψ)

/-- The source average-error infimum over measurable tests. -/
noncomputable def averageErrorInfimum (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] : ℝ :=
  sInf (Set.range (averageTestError P))

/-- The source minimax-error infimum over measurable tests. -/
noncomputable def minimaxErrorInfimum (P : I → Measure Ω)
    [∀ i, IsProbabilityMeasure (P i)] : ℝ :=
  sInf (Set.range (worstTestError P))


end Testing

end StatisticalRL.PrelimFano

import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Measure.Map

/-! Canonical Chapter 2 Fano testing foundations. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace StatisticalRL.PrelimFano

def fiberOf {Ω Ξ : Type*} (f : Ω → Ξ) (y : Ξ) : Set Ω :=
  f ⁻¹' ({y} : Set Ξ)


end StatisticalRL.PrelimFano

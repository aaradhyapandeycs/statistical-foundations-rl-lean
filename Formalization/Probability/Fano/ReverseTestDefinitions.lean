import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Canonical Chapter 2 Fano testing foundations. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatisticalRL.PrelimFano

/-- The Boolean indicator of a set. -/
noncomputable def eventIndicatorBool {Ω : Type*} (A : Set Ω) : Ω → Bool :=
  fun ω => by classical exact decide (ω ∈ A)


/-- The probability of a set, as a Bernoulli parameter. -/
noncomputable def eventParam {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) : ℝ≥0 :=
  (P A).toNNReal


end StatisticalRL.PrelimFano

import Formalization.MDP.CoreDefinitions
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Constructions.Pi

/-! Finite sampling laws and empirical frequencies. -/
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace StatisticalRL

/-- Conversion from the project's real-valued finite probability law into a
Mathlib probability mass function; no mass or normalization is changed. -/
noncomputable def FiniteDistribution.toPMF {Ω : Type*} [Fintype Ω]
    (d : FiniteDistribution Ω) : PMF Ω :=
  PMF.ofFintype (fun x ↦ ENNReal.ofReal (d.prob x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ d.prob_nonneg x), d.sum_prob]
    exact ENNReal.ofReal_one)

namespace FiniteDistribution
variable {State : Type*} [Fintype State]
local instance finiteSampleStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance finiteSampleStateDecidable : DecidableEq State := Classical.decEq State

/-- The probability measure of one draw from the actual transition row. -/
noncomputable def rowMeasure (d : FiniteDistribution State) : Measure State :=
  d.toPMF.toMeasure

/-- The genuine independent product law for `N` observations of one row. -/
noncomputable def sampleMeasure (d : FiniteDistribution State) (N : ℕ) :
    Measure (Fin N → State) := Measure.pi (fun _ ↦ d.rowMeasure)

/-- The empirical frequency row of an observed sample, for positive `N`. -/
noncomputable def empiricalRow (N : ℕ) (hN : 0 < N) (ω : Fin N → State) :
    FiniteDistribution State where
  prob s := (N : ℝ)⁻¹ * ∑ i, if ω i = s then 1 else 0
  prob_nonneg s := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
    (Finset.sum_nonneg (fun _ _ ↦ by split <;> norm_num))
  sum_prob := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    simp [ne_of_gt hN]

end FiniteDistribution
end StatisticalRL

import Formalization.Probability.EmpiricalBernsteinSharp.FiniteProductMass
import Formalization.Probability.EmpiricalRow

/-! Private uncompiled bridge from the finite product sums to the actual iid
row-sampling measure. -/
open scoped BigOperators
open MeasureTheory
namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance productEntropyStateMeasurable : MeasurableSpace State := ⊤

/-- Integrating an arbitrary real function of the complete sample under the
actual iid row law is the corresponding finite product-mass sum. -/
theorem sampleMeasure_integral_product_mass (d : FiniteDistribution State)
    (n : ℕ) (F : (Fin n → State) → ℝ) :
    ∫ ω, F ω ∂d.sampleMeasure n =
      ∑ ω : Fin n → State, (∏ i, d.prob (ω i)) * F ω := by
  classical
  have hs (s : State) : d.rowMeasure {s} = ENNReal.ofReal (d.prob s) := by
    rw [rowMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    exact d.toPMF_apply s
  rw [MeasureTheory.integral_fintype F Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro ω hω
  simp only [smul_eq_mul, Measure.real, sampleMeasure, Measure.pi_singleton,
    ENNReal.toReal_prod, hs, ENNReal.toReal_ofReal (d.prob_nonneg _)]

end StatisticalRL.FiniteDistribution

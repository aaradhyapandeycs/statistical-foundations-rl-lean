import Formalization.Online.QLearning.WeightedRowMGF

/-! Fixed product-row weighted tail, private and not yet compiler checked. -/
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteDistribution
variable {State : Type*} [Fintype State]
local instance qLearningWeightedTailStateMeasurable : MeasurableSpace State := ⊤

/-- Two-sided tail for deterministic weights and a fixed bounded vector.
This includes zero proxy using Mathlib's totalized real division. -/
theorem qLearning_weightedRow_twoSided (d : FiniteDistribution State)
    (V : State → ℝ) (N : ℕ) (B t : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B)
    (w : Fin N → ℝ) (ht : 0 ≤ t) :
    (d.sampleMeasure N).real {ω | t ≤ |∑ i : Fin N, w i * d.centeredSample V N i ω|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ((∑ i : Fin N, ‖w i‖₊ ^ 2 * (‖B‖₊ / 2)^2 : ℝ≥0) : ℝ))) := by
  let S : (Fin N → State) → ℝ := fun ω ↦ ∑ i : Fin N, w i * d.centeredSample V N i ω
  have hsg := d.qLearning_weightedRow_subgaussian V N B hV w
  change HasSubgaussianMGF S _ _ at hsg
  have hp := hsg.measure_ge_le ht
  have hn := hsg.neg.measure_ge_le ht
  calc
    (d.sampleMeasure N).real {ω | t ≤ |S ω|} ≤
        (d.sampleMeasure N).real ({ω | t ≤ S ω} ∪ {ω | t ≤ -S ω}) := by
          apply measureReal_mono ?_ (measure_ne_top _ _)
          intro ω hω
          change t ≤ |S ω| at hω
          change t ≤ S ω ∨ t ≤ -S ω
          exact (le_abs).mp hω
    _ ≤ (d.sampleMeasure N).real {ω | t ≤ S ω} +
        (d.sampleMeasure N).real {ω | t ≤ -S ω} := measureReal_union_le _ _
    _ ≤ _ := by simpa only [Pi.neg_apply, two_mul] using add_le_add hp hn
end StatisticalRL.FiniteDistribution

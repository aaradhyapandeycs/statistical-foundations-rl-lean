import Formalization.Probability.EmpiricalRowMeasurableDefinitions
import Formalization.Probability.FiniteSampleDefinitions
import Formalization.MDP.InfiniteTrajectory
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Independent samples and empirical transition rows

For a finite transition row, sample `N` states independently from the actual
row law. When `N > 0`, empirical frequencies form a probability vector and
its evaluation is the average of the observed values.
Source: Chapter 2, lines 916–927 of arXiv:2610.41903v1.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
attribute [local instance] empiricalRowStateMeasurable

noncomputable local instance empiricalRowStateDecidable : DecidableEq State := Classical.decEq State

instance rowMeasure_isProbabilityMeasure (d : FiniteDistribution State) :
    IsProbabilityMeasure d.rowMeasure := inferInstanceAs
      (IsProbabilityMeasure d.toPMF.toMeasure)

instance sampleMeasure_isProbabilityMeasure (d : FiniteDistribution State) (N : ℕ) :
    IsProbabilityMeasure (d.sampleMeasure N) := by
  unfold sampleMeasure
  infer_instance

/-- Every observation has the given transition row as its marginal law. -/
theorem sampleMeasure_coordinate (d : FiniteDistribution State) (N : ℕ) (i : Fin N) :
    (d.sampleMeasure N).map (fun ω ↦ ω i) = d.rowMeasure := by
  exact (measurePreserving_eval (fun _ : Fin N ↦ d.rowMeasure) i).map_eq

/-- Each coordinate assigns the source transition mass to every state. -/
theorem sampleMeasure_coordinate_singleton (d : FiniteDistribution State)
    (N : ℕ) (i : Fin N) (s : State) :
    d.sampleMeasure N {ω | ω i = s} = ENNReal.ofReal (d.prob s) := by
  change d.sampleMeasure N ((fun ω : Fin N → State ↦ ω i) ⁻¹' {s}) = _
  rw [← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton s),
    sampleMeasure_coordinate, rowMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rfl

/-- The actual sample coordinate variables are mutually independent. -/
theorem sampleMeasure_independent (d : FiniteDistribution State) (N : ℕ) :
    iIndepFun (fun i (ω : Fin N → State) ↦ ω i) (d.sampleMeasure N) := by
  exact iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)

/-- Evaluating the frequency row at `V` equals the empirical sample mean. -/
theorem empiricalRow_expectation (N : ℕ) (hN : 0 < N) (ω : Fin N → State)
    (V : State → ℝ) :
    (empiricalRow N hN ω).expectation V = (N : ℝ)⁻¹ * ∑ i, V (ω i) := by
  simp only [expectation, empiricalRow]
  simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp

/-- Integrating a value under the actual row measure is its finite expectation. -/
theorem rowMeasure_integral (d : FiniteDistribution State) (V : State → ℝ) :
    ∫ x, V x ∂d.rowMeasure = d.expectation V := by
  rw [rowMeasure, PMF.integral_eq_sum]
  simp [expectation, toPMF_apply, ENNReal.toReal_ofReal, d.prob_nonneg]

/-- Each sampled value has the original row expectation. -/
theorem sampleMeasure_coordinate_integral (d : FiniteDistribution State)
    (N : ℕ) (i : Fin N) (V : State → ℝ) :
    ∫ ω, V (ω i) ∂(d.sampleMeasure N) = d.expectation V := by
  rw [← rowMeasure_integral d V, ← sampleMeasure_coordinate d N i]
  exact (integral_map (measurable_pi_apply i).aemeasurable
    (Integrable.of_finite : Integrable V ((d.sampleMeasure N).map (fun ω ↦ ω i))).aestronglyMeasurable).symm

/-- The empirical row evaluation is unbiased for the true row evaluation. -/
theorem empiricalRow_unbiased (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N)
    (V : State → ℝ) :
    ∫ ω, (empiricalRow N hN ω).expectation V ∂(d.sampleMeasure N) = d.expectation V := by
  simp_rw [empiricalRow_expectation]
  rw [integral_const_mul, integral_finset_sum]
  · simp_rw [sampleMeasure_coordinate_integral]
    simp [ne_of_gt hN]
  · intro i hi
    exact Integrable.of_finite

end StatisticalRL.FiniteDistribution

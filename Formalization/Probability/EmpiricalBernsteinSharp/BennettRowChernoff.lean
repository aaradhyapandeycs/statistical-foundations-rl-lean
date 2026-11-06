import Formalization.Probability.EmpiricalBernsteinSharp.BennettExactRowMGF

/-! Private uncompiled intermediate: the actual iid empirical-row law has the
Bennett Chernoff exponent for every nonnegative parameter. This is not the
empirical Bernstein theorem. -/

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]

theorem empiricalRow_upper_bennett_chernoff (d : FiniteDistribution State)
    (V : State → ℝ) (N : ℕ) (hN : 0 < N) (B ε u : ℝ)
    (hB : 0 < B) (hu : 0 ≤ u) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real
        {ω | ε ≤ (empiricalRow N hN ω).expectation V - d.expectation V} ≤
      Real.exp (-u * ((N : ℝ) * ε) + (N : ℝ) *
        (((Real.exp (u*B) - 1 - u*B) / B^2) * d.variance V)) := by
  have hmgf := d.centeredRow_mgf_le_bennett V B u hB hu hV
  have hnonneg : 0 ≤ ProbabilityTheory.mgf
      (fun s ↦ V s - d.expectation V) d.rowMeasure u := ProbabilityTheory.mgf_nonneg
  calc
    _ ≤ Real.exp (-u * ((N : ℝ) * ε)) *
        (ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u)^N :=
      d.empiricalRow_chernoff_mgf V N hN ε u hu
    _ ≤ Real.exp (-u * ((N : ℝ) * ε)) *
        (Real.exp (((Real.exp (u*B) - 1 - u*B) / B^2) * d.variance V))^N := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hmgf N) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

end StatisticalRL.FiniteDistribution

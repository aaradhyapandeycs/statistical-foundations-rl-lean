import Formalization.Probability.EmpiricalBernsteinSharp.BennettRowChernoff
import Formalization.Probability.EmpiricalBernsteinSharp.BennettInverseScalar

/-! Private uncompiled positive-variance Bennett optimization. The zero-range
and zero-variance cases require the separate existing zero-variance tail. -/

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]

theorem empiricalRow_upper_bennett_optimized (d : FiniteDistribution State)
    (V : State → ℝ) (N : ℕ) (hN : 0 < N) (B ε : ℝ)
    (hB : 0 < B) (hε : 0 ≤ ε) (hv : 0 < d.variance V)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real
        {ω | ε ≤ (empiricalRow N hN ω).expectation V - d.expectation V} ≤
      Real.exp (-((N : ℝ) * d.variance V / B^2) *
        ((1 + B*ε/d.variance V) * Real.log (1 + B*ε/d.variance V) -
          B*ε/d.variance V)) := by
  let z : ℝ := B*ε/d.variance V
  have hz : 0 ≤ z := div_nonneg (mul_nonneg hB.le hε) hv.le
  have hlog : 0 ≤ Real.log (1+z) := Real.log_nonneg (by linarith)
  let u : ℝ := Real.log (1+z)/B
  have hu : 0 ≤ u := div_nonneg hlog hB.le
  have hexp : Real.exp (u*B) = 1+z := by
    have heq : u*B = Real.log (1+z) := by
      dsimp [u]
      field_simp
    rw [heq, Real.exp_log (by linarith : 0 < 1+z)]
  have h := d.empiricalRow_upper_bennett_chernoff V N hN B ε u hB hu hV
  have heq : -u*((N : ℝ)*ε) + (N : ℝ)*
      (((Real.exp (u*B)-1-u*B)/B^2)*d.variance V) =
      -((N : ℝ)*d.variance V/B^2)*
        ((1+B*ε/d.variance V)*Real.log (1+B*ε/d.variance V)-B*ε/d.variance V) := by
    rw [hexp]
    dsimp [u, z]
    field_simp
    <;> ring
  rwa [heq] at h

end StatisticalRL.FiniteDistribution

import Formalization.Probability.EmpiricalBernsteinSharp.BennettPositiveRemainder
import Formalization.Probability.EmpiricalBernsteinSharp.BennettNegativeRemainder

/-! Private, uncompiled Bennett row-MGF candidate. This is an intermediate
estimate, not a claim that the empirical Bernstein source result is proved. -/

namespace StatisticalRL.SharpBernstein

theorem exp_remainder_scaled_le (a x : ℝ) (ha : 0 ≤ a) (hx : x ≤ 1) :
    Real.exp (a*x) ≤ 1 + a*x + x^2 * (Real.exp a - 1 - a) := by
  by_cases h : 0 ≤ x
  · exact exp_remainder_scaled_nonnegative a x ha h hx
  · exact exp_remainder_scaled_nonpositive a x ha (le_of_not_ge h)

end StatisticalRL.SharpBernstein

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance bennettRowStateMeasurable : MeasurableSpace State := ⊤

/-- Exact Bennett MGF for a bounded finite row, without a small-parameter
restriction. -/
theorem centeredRow_mgf_le_bennett (d : FiniteDistribution State) (V : State → ℝ)
    (B u : ℝ) (hB : 0 < B) (hu : 0 ≤ u)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u ≤
      Real.exp (((Real.exp (u*B) - 1 - u*B) / B^2) * d.variance V) := by
  have hμ0 : 0 ≤ d.expectation V := d.expectation_nonneg (fun s ↦ (hV s).1)
  have hpoint (s : State) :
      Real.exp (u * (V s - d.expectation V)) ≤
        1 + u * (V s - d.expectation V) +
          ((Real.exp (u*B) - 1 - u*B) / B^2) * (V s - d.expectation V)^2 := by
    have hx : (V s - d.expectation V) / B ≤ 1 := by
      apply (div_le_one hB).2
      linarith [(hV s).2]
    have hp := StatisticalRL.SharpBernstein.exp_remainder_scaled_le
      (u*B) ((V s - d.expectation V)/B) (mul_nonneg hu hB.le) hx
    have harg : (u*B) * ((V s - d.expectation V)/B) =
        u * (V s - d.expectation V) := by field_simp
    have hcoef : ((V s - d.expectation V)/B)^2 * (Real.exp (u*B) - 1 - u*B) =
        ((Real.exp (u*B) - 1 - u*B) / B^2) * (V s - d.expectation V)^2 := by
      field_simp
      <;> ring
    rw [harg, hcoef] at hp
    exact hp
  have hmean : d.expectation (fun s ↦ V s - d.expectation V) = 0 := by
    rw [d.expectation_sub, d.expectation_const, sub_self]
  calc
    ProbabilityTheory.mgf (fun s ↦ V s - d.expectation V) d.rowMeasure u =
        d.expectation (fun s ↦ Real.exp (u * (V s - d.expectation V))) := by
      exact d.rowMeasure_integral _
    _ ≤ d.expectation (fun s ↦ 1 + u * (V s - d.expectation V) +
        ((Real.exp (u*B) - 1 - u*B) / B^2) * (V s - d.expectation V)^2) :=
      d.expectation_mono hpoint
    _ = 1 + ((Real.exp (u*B) - 1 - u*B) / B^2) * d.variance V := by
      rw [d.expectation_add, d.expectation_add, d.expectation_const,
        d.expectation_mul, d.expectation_mul, hmean,
        ← d.variance_eq_expectation_centered_sq]
      ring
    _ ≤ Real.exp (((Real.exp (u*B) - 1 - u*B) / B^2) * d.variance V) := by
      linarith [Real.add_one_le_exp
        (((Real.exp (u*B) - 1 - u*B) / B^2) * d.variance V)]

end StatisticalRL.FiniteDistribution

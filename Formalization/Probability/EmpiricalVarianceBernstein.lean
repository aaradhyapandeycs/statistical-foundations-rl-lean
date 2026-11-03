import Formalization.Probability.EmpiricalBernstein

/-! Actual sample-row variance identities for the empirical Bernstein source bound. -/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance empiricalVarianceStateMeasurable : MeasurableSpace State := ⊤

/-- The source's empirical variance, using the actual frequency row. -/
noncomputable def empiricalVariance (N : ℕ) (hN : 0 < N)
    (V : State → ℝ) (ω : Fin N → State) : ℝ :=
  (empiricalRow N hN ω).variance V

theorem empiricalVariance_nonneg (N : ℕ) (hN : 0 < N) (V : State → ℝ)
    (ω : Fin N → State) : 0 ≤ empiricalVariance N hN V ω :=
  (empiricalRow N hN ω).variance_nonneg V

/-- The exact downward bias for the variance with source denominator N. -/
theorem empiricalVariance_integral (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (V : State → ℝ) :
    ∫ ω, empiricalVariance N hN V ω ∂(d.sampleMeasure N) =
      ((N : ℝ) - 1) / N * d.variance V := by
  let X : (Fin N → State) → ℝ := fun ω ↦ (empiricalRow N hN ω).expectation V
  have hm := ProbabilityTheory.variance_eq_sub (d.empiricalValue_memLp V N hN)
  change ProbabilityTheory.variance X (d.sampleMeasure N) =
    (∫ ω, (X ^ 2) ω ∂(d.sampleMeasure N)) - (∫ ω, X ω ∂(d.sampleMeasure N)) ^ 2 at hm
  have hv : ProbabilityTheory.variance X (d.sampleMeasure N) = d.variance V / N :=
    d.empiricalValue_variance V N hN
  have hx : ∫ ω, X ω ∂(d.sampleMeasure N) = d.expectation V :=
    d.empiricalRow_unbiased N hN V
  rw [hv, hx] at hm
  have hp : (∫ ω, (X ω) ^ 2 ∂(d.sampleMeasure N)) =
      d.variance V / N + (d.expectation V) ^ 2 := by
    simpa only [Pi.pow_apply] using (eq_add_of_sub_eq hm.symm)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  unfold empiricalVariance variance
  rw [integral_sub Integrable.of_finite Integrable.of_finite,
    d.empiricalRow_unbiased N hN (fun s ↦ V s ^ 2)]
  change d.expectation (fun s ↦ V s ^ 2) - (∫ ω, (X ω) ^ 2 ∂(d.sampleMeasure N)) = _
  rw [hp]
  unfold FiniteDistribution.variance
  field_simp
  ring

/-- For N≥2, the usual N/(N−1) correction is unbiased under the true iid law. -/
theorem correctedEmpiricalVariance_unbiased (d : FiniteDistribution State) (N : ℕ)
    (hN2 : 2 ≤ N) (V : State → ℝ) :
    let hN : 0 < N := by omega
    ∫ ω, ((N : ℝ) / (N - 1)) * empiricalVariance N hN V ω ∂(d.sampleMeasure N) =
      d.variance V := by
  intro hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hn1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  rw [integral_const_mul, d.empiricalVariance_integral N hN V]
  field_simp

/-- The empirical variance itself is bounded by the square of the range over four. -/
theorem variance_le_range_sq_div_four (d : FiniteDistribution State) (V : State → ℝ)
    (B : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    d.variance V ≤ B ^ 2 / 4 := by
  have hm0 : 0 ≤ d.expectation V := d.expectation_nonneg (fun s ↦ (hV s).1)
  have hmB : d.expectation V ≤ B := d.expectation_le_const (fun s ↦ (hV s).2)
  have hs : d.expectation (fun s ↦ V s ^ 2) ≤ d.expectation (fun s ↦ B * V s) := by
    apply d.expectation_mono
    intro s
    nlinarith [(hV s).1, (hV s).2]
  rw [d.expectation_mul] at hs
  unfold variance
  nlinarith [sq_nonneg (d.expectation V - B / 2)]

theorem empiricalVariance_le_range_sq_div_four (N : ℕ) (hN : 0 < N)
    (V : State → ℝ) (B : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B)
    (ω : Fin N → State) : empiricalVariance N hN V ω ≤ B ^ 2 / 4 :=
  (empiricalRow N hN ω).variance_le_range_sq_div_four V B hV

/-- A deterministic comparison reduces empirical-variance error to first- and second-moment errors. -/
theorem empiricalVariance_abs_sub_le (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (V : State → ℝ) (B : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 B)
    (ω : Fin N → State) :
    |empiricalVariance N hN V ω - d.variance V| ≤
      |(empiricalRow N hN ω).expectation (fun s ↦ V s ^ 2) -
        d.expectation (fun s ↦ V s ^ 2)| +
      2 * B * |(empiricalRow N hN ω).expectation V - d.expectation V| := by
  let q := empiricalRow N hN ω
  have hq0 : 0 ≤ q.expectation V := q.expectation_nonneg (fun s ↦ (hV s).1)
  have hqB : q.expectation V ≤ B := q.expectation_le_const (fun s ↦ (hV s).2)
  have hd0 : 0 ≤ d.expectation V := d.expectation_nonneg (fun s ↦ (hV s).1)
  have hdB : d.expectation V ≤ B := d.expectation_le_const (fun s ↦ (hV s).2)
  have hsquare : |q.expectation V ^ 2 - d.expectation V ^ 2| ≤
      2 * B * |q.expectation V - d.expectation V| := by
    apply StatisticalRL.abs_sq_sub_sq_le (abs_nonneg _)
    · rwa [abs_of_nonneg hq0]
    · rwa [abs_of_nonneg hd0]
    · exact le_rfl
  change |q.variance V - d.variance V| ≤ _
  unfold variance
  calc
    _ = |(q.expectation (fun s ↦ V s ^ 2) - d.expectation (fun s ↦ V s ^ 2)) -
        (q.expectation V ^ 2 - d.expectation V ^ 2)| := by congr 1 <;> ring
    _ ≤ |q.expectation (fun s ↦ V s ^ 2) - d.expectation (fun s ↦ V s ^ 2)| +
        |q.expectation V ^ 2 - d.expectation V ^ 2| := abs_sub _ _
    _ ≤ _ := by
      dsimp only [q] at hsquare ⊢
      exact add_le_add le_rfl hsquare

/-- On every sample, a nonnegative vector's empirical mean differs from its true mean by at most its sup norm. -/
theorem empiricalRow_abs_deviation_le_norm (d : FiniteDistribution State) (N : ℕ)
    (hN : 0 < N) (V : State → ℝ) (hV : ∀ s, 0 ≤ V s) (ω : Fin N → State) :
    |(empiricalRow N hN ω).expectation V - d.expectation V| ≤ ‖V‖ := by
  have hv (s : State) : V s ≤ ‖V‖ := (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm V s)
  have h10 : 0 ≤ (empiricalRow N hN ω).expectation V :=
    (empiricalRow N hN ω).expectation_nonneg hV
  have h11 : (empiricalRow N hN ω).expectation V ≤ ‖V‖ :=
    (empiricalRow N hN ω).expectation_le_const hv
  have h20 : 0 ≤ d.expectation V := d.expectation_nonneg hV
  have h21 : d.expectation V ≤ ‖V‖ := d.expectation_le_const hv
  apply abs_le.mpr
  constructor <;> linarith

/-- The exact source radius succeeds surely when its linear term dominates the range. -/
theorem empiricalBernstein_fixedRow_smallConfidence (d : FiniteDistribution State)
    (N : ℕ) (hN2 : 2 ≤ N) (V : State → ℝ) (hV : ∀ s, 0 ≤ V s)
    (δ : ℝ) (hδ : 0 < δ)
    (hsmall : 3 * ((N : ℝ) - 1) ≤ 7 * Real.log (4 / δ)) :
    let hN : 0 < N := by omega
    1 - δ < (d.sampleMeasure N).real {ω |
      |(empiricalRow N hN ω).expectation V - d.expectation V| ≤
        Real.sqrt (2 * Real.log (4 / δ) / ((N : ℝ) - 1)) *
          Real.sqrt (empiricalVariance N hN V ω) +
        7 * ‖V‖ * Real.log (4 / δ) / (3 * ((N : ℝ) - 1))} := by
  intro hN
  have hn : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hden : 0 < 3 * ((N : ℝ) - 1) := by positivity
  have hlin : ‖V‖ ≤ 7 * ‖V‖ * Real.log (4 / δ) / (3 * ((N : ℝ) - 1)) := by
    apply (le_div_iff₀ hden).2
    have hmul := mul_nonneg (norm_nonneg V) (sub_nonneg.mpr hsmall)
    nlinarith
  have hall (ω : Fin N → State) :
      |(empiricalRow N hN ω).expectation V - d.expectation V| ≤
        Real.sqrt (2 * Real.log (4 / δ) / ((N : ℝ) - 1)) *
          Real.sqrt (empiricalVariance N hN V ω) +
        7 * ‖V‖ * Real.log (4 / δ) / (3 * ((N : ℝ) - 1)) := by
    have hsq : 0 ≤ Real.sqrt (2 * Real.log (4 / δ) / ((N : ℝ) - 1)) *
        Real.sqrt (empiricalVariance N hN V ω) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith [d.empiricalRow_abs_deviation_le_norm N hN V hV ω]
  have heq : {ω : Fin N → State |
      |(empiricalRow N hN ω).expectation V - d.expectation V| ≤
        Real.sqrt (2 * Real.log (4 / δ) / ((N : ℝ) - 1)) *
          Real.sqrt (empiricalVariance N hN V ω) +
        7 * ‖V‖ * Real.log (4 / δ) / (3 * ((N : ℝ) - 1))} = Set.univ := by
    ext ω
    simp [hall ω]
  rw [heq, probReal_univ]
  linarith

end StatisticalRL.FiniteDistribution

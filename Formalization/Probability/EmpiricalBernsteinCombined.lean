import Formalization.Probability.SelfBoundingConcentration
import Formalization.Probability.SharpEmpiricalBernstein

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteDistribution
variable {State : Type*} [Fintype State]
local instance combinedStateMeasurable : MeasurableSpace State := ⊤

/-- A fixed-vector empirical Bernstein bound with non-sharp explicit constants. -/
theorem empiricalBernstein_combined_exp (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B x : ℝ) (hB : 0 < B) (hx : 0 < x)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω |
      Real.sqrt (2 * x / N) * (Real.sqrt (empiricalVariance N hN V ω) +
        4 * B * Real.sqrt (x / N)) + 2 * B * x / (3 * N) <
      |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤
      5 * Real.exp (-x) := by
  let A : Set (Fin N → State) := {ω |
    Real.sqrt (2 * x * d.variance V / N) + 2 * B * x / (3 * N) <
      |(empiricalRow N hN ω).expectation V - d.expectation V|}
  let C : Set (Fin N → State) := {ω | Real.sqrt (empiricalVariance N hN V ω) +
    4 * B * Real.sqrt (x / N) < Real.sqrt (d.variance V)}
  have hA := d.empiricalRow_source_threshold_strict V N hN B x hB.le hx hV
  have hC := d.empiricalStd_lower_tail_exp V N hN B x hB hx hV
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : Real.sqrt (2 * x * d.variance V / N) =
      Real.sqrt (2 * x / N) * Real.sqrt (d.variance V) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * x / N)]
    congr 1
    ring
  have hsub : {ω | Real.sqrt (2 * x / N) *
      (Real.sqrt (empiricalVariance N hN V ω) + 4 * B * Real.sqrt (x / N)) +
      2 * B * x / (3 * N) <
      |(empiricalRow N hN ω).expectation V - d.expectation V|} ⊆ A ∪ C := by
    intro ω hw
    simp only [Set.mem_setOf_eq] at hw
    by_contra hnot
    have hc : Real.sqrt (d.variance V) ≤ Real.sqrt (empiricalVariance N hN V ω) +
        4 * B * Real.sqrt (x / N) := le_of_not_gt (fun h ↦ hnot (Set.mem_union_right A h))
    have ha := mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg (2 * x / N))
    have hb : ω ∈ A := by
      dsimp [A]
      rw [hsqrt]
      linarith
    exact hnot (Set.mem_union_left C hb)
  calc
    _ ≤ (d.sampleMeasure N).real (A ∪ C) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (d.sampleMeasure N).real A + (d.sampleMeasure N).real C := measureReal_union_le _ _
    _ ≤ 5 * Real.exp (-x) := by linarith

/-- Observable fixed-vector confidence radius for the actual iid empirical row. -/
theorem empiricalBernstein_combined_confidence (d : FiniteDistribution State) (V : State → ℝ)
    (N : ℕ) (hN : 0 < N) (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω |
      Real.sqrt (2 * Real.log (5 / δ) / N) * (Real.sqrt (empiricalVariance N hN V ω) +
        4 * B * Real.sqrt (Real.log (5 / δ) / N)) +
        2 * B * Real.log (5 / δ) / (3 * N) <
      |(empiricalRow N hN ω).expectation V - d.expectation V|} ≤ δ := by
  have hratio : 1 < 5 / δ := (lt_div_iff₀ hδ).2 (by linarith)
  have h := d.empiricalBernstein_combined_exp V N hN B (Real.log (5 / δ)) hB
    (Real.log_pos hratio) hV
  have heq : 5 * Real.exp (-Real.log (5 / δ)) = δ := by
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 5 / δ)]
    field_simp
  rwa [heq] at h

end StatisticalRL.FiniteDistribution

import Formalization.Probability.EmpiricalBernsteinSharp.EmpiricalVarianceLowerTail
import Formalization.Probability.EmpiricalBernsteinSharp.EmpiricalStdTailInversion

/-! Private uncompiled population-standard-deviation confidence bound. -/
open scoped BigOperators
open MeasureTheory
namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance empiricalStdTailStateMeasurable : MeasurableSpace State := ⊤

theorem empiricalStd_population_exceedance (d : FiniteDistribution State)
    (N : ℕ) (hN2 : 2 ≤ N) (V : State → ℝ) (B t : ℝ)
    (hB : 0 < B) (ht : 0 < t) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    let hN : 0 < N := by omega
    (d.sampleMeasure N).real {ω |
      Real.sqrt (d.variance V) >
        Real.sqrt ((N : ℝ)/((N : ℝ)-1) * empiricalVariance N hN V ω) +
          B*Real.sqrt (2*t/((N : ℝ)-1))} ≤ Real.exp (-t) := by
  let hN : 0 < N := by omega
  have hn : (1 : ℝ) < N := by
    have h : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have htail := d.normalizedUnbiasedVariance_lower_tail N hN2 V B t hB ht hV
  calc
    _ ≤ (d.sampleMeasure N).real {ω |
        Real.sqrt (2*((N : ℝ)/((N : ℝ)-1))*((N : ℝ)*d.variance V/B^2)*t) <
          (N : ℝ)*d.variance V/B^2-normalizedUnbiasedVariance N hN2 V B ω} := by
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      have hh := StatisticalRL.Probability.empirical_std_exceedance_implies_selfbound_deviation
        (N : ℝ) B (d.variance V) (empiricalVariance N hN V ω) t hn hB
        (d.variance_nonneg V) (empiricalVariance_nonneg N hN V ω) ht.le hω
      simpa only [normalizedUnbiasedVariance] using hh
    _ ≤ Real.exp (-t) := htail

end StatisticalRL.FiniteDistribution

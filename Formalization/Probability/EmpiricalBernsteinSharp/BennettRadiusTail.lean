import Formalization.Probability.EmpiricalBernsteinSharp.BennettTuning
import Formalization.Probability.EmpiricalBernsteinSharp.BennettScaledInverse

/-! Private uncompiled fixed-vector Bennett radius for the actual iid row.
No empirical-variance concentration or random-family theorem is asserted. -/
open MeasureTheory
namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]

theorem empiricalRow_upper_bennett_radius_positive (d : FiniteDistribution State)
    (V : State → ℝ) (N : ℕ) (hN : 0 < N) (B t : ℝ)
    (hB : 0 < B) (ht : 0 ≤ t) (hv : 0 < d.variance V)
    (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω |
      Real.sqrt (2*d.variance V*t/N) + B*t/(3*N) ≤
        (empiricalRow N hN ω).expectation V - d.expectation V} ≤ Real.exp (-t) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let ε : ℝ := Real.sqrt (2*d.variance V*t/N) + B*t/(3*N)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have htail := d.empiricalRow_upper_bennett_optimized V N hN B ε hB hε hv hV
  have hscale := StatisticalRL.SharpBernstein.bennett_scaled_inverse
    (N : ℝ) (d.variance V) B t hn hv hB ht
  change t ≤ ((N : ℝ)*d.variance V/B^2) *
    ((1+B*ε/d.variance V)*Real.log (1+B*ε/d.variance V)-B*ε/d.variance V) at hscale
  calc
    _ ≤ Real.exp (-((N : ℝ)*d.variance V/B^2) *
      ((1+B*ε/d.variance V)*Real.log (1+B*ε/d.variance V)-B*ε/d.variance V)) := htail
    _ ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)

/-- Strict upper deviation, including zero range and zero variance. -/
theorem empiricalRow_upper_bennett_radius_strict (d : FiniteDistribution State)
    (V : State → ℝ) (N : ℕ) (hN : 0 < N) (B t : ℝ)
    (hB : 0 ≤ B) (ht : 0 < t) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω |
      Real.sqrt (2*d.variance V*t/N) + B*t/(3*N) <
        (empiricalRow N hN ω).expectation V - d.expectation V} ≤ Real.exp (-t) := by
  let ε : ℝ := Real.sqrt (2*d.variance V*t/N) + B*t/(3*N)
  by_cases hv : 0 < d.variance V
  · have hBp : 0 < B := by
      by_contra h
      have hzero : B = 0 := le_antisymm (le_of_not_gt h) hB
      have hVzero : V = fun _ ↦ 0 := by
        funext s
        have hs := hV s
        rw [hzero] at hs
        exact le_antisymm hs.2 hs.1
      subst V
      simp at hv
    have htail := d.empiricalRow_upper_bennett_radius_positive V N hN B t hBp ht.le hv hV
    calc
      _ ≤ (d.sampleMeasure N).real {ω | ε ≤
          (empiricalRow N hN ω).expectation V - d.expectation V} := by
        apply measureReal_mono ?_ (measure_ne_top _ _)
        intro ω hω
        change ε < (empiricalRow N hN ω).expectation V - d.expectation V at hω
        exact le_of_lt hω
      _ ≤ Real.exp (-t) := htail
  · have hv0 : d.variance V = 0 := le_antisymm (le_of_not_gt hv) (d.variance_nonneg V)
    by_cases hB0 : B = 0
    · have hzero : V = fun _ ↦ 0 := by
        funext s
        have hs := hV s
        rw [hB0] at hs
        exact le_antisymm hs.2 hs.1
      subst V
      have hε : 0 ≤ ε := by dsimp [ε]; positivity
      have hempty : {ω : Fin N → State | ε <
          (empiricalRow N hN ω).expectation (fun _ ↦ 0) - d.expectation (fun _ ↦ 0)} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rw [FiniteDistribution.expectation_const, FiniteDistribution.expectation_const, sub_self]
        exact not_lt_of_ge hε
      rw [hempty, measureReal_empty]
      positivity
    · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
      have hn : (0 : ℝ) < N := by exact_mod_cast hN
      have hε : 0 < ε := by dsimp [ε]; positivity
      have hz := d.empiricalRow_zeroVariance_sharp V N hN ε hε hv0
      calc
        _ ≤ (d.sampleMeasure N).real {ω | ε ≤
            |(empiricalRow N hN ω).expectation V - d.expectation V|} := by
          apply measureReal_mono ?_ (measure_ne_top _ _)
          intro ω hω
          change ε < (empiricalRow N hN ω).expectation V - d.expectation V at hω
          exact le_trans (le_of_lt hω) (le_abs_self _)
        _ = 0 := hz
        _ ≤ Real.exp (-t) := by positivity

end StatisticalRL.FiniteDistribution

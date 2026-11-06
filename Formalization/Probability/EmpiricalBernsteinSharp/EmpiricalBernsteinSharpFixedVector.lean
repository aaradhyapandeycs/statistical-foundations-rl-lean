import Formalization.Probability.EmpiricalBernsteinSharp.BennettRadiusTail
import Formalization.Probability.EmpiricalBernsteinSharp.EmpiricalStdLowerTail
import Formalization.Probability.EmpiricalBernsteinSharp.EmpiricalBernsteinSharpRadiusAlgebra

/-! Private uncompiled fixed-vector empirical Bernstein candidate with the
literal 7/3 constant. The random-family source theorem remains separate. -/
open scoped BigOperators
open MeasureTheory
namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance sharpFixedVectorStateMeasurable : MeasurableSpace State := ⊤

theorem empiricalRow_empiricalBernstein_fixed_failure (d : FiniteDistribution State)
    (N : ℕ) (hN2 : 2 ≤ N) (V : State → ℝ) (B t : ℝ)
    (hB : 0 ≤ B) (ht : 0 < t) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    let hN : 0 < N := by omega
    (d.sampleMeasure N).real {ω |
      Real.sqrt (2*empiricalVariance N hN V ω*t/((N : ℝ)-1)) +
          7*B*t/(3*((N : ℝ)-1)) <
        |(empiricalRow N hN ω).expectation V-d.expectation V|} ≤ 3*Real.exp (-t) := by
  classical
  let hN : 0 < N := by omega
  let D : (Fin N → State) → ℝ := fun ω ↦
    (empiricalRow N hN ω).expectation V-d.expectation V
  let r : ℝ := Real.sqrt (2*d.variance V*t/N)+B*t/(3*N)
  by_cases hB0 : B = 0
  · have hzero : V = fun _ ↦ 0 := by
      funext s
      have hs := hV s
      rw [hB0] at hs
      exact le_antisymm hs.2 hs.1
    subst V
    simp [D, empiricalVariance, variance, expectation_const, hB0] <;> positivity
  · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hn : (1 : ℝ) < N := by
      have h : (2 : ℝ) ≤ N := by exact_mod_cast hN2
      linarith
    have hp := d.empiricalRow_upper_bennett_radius_strict V N hN B t hB ht hV
    let W : State → ℝ := fun s ↦ B-V s
    have hw (s : State) : W s ∈ Set.Icc 0 B := by
      dsimp [W]
      constructor <;> linarith [(hV s).1, (hV s).2]
    have hv : d.variance W = d.variance V := d.variance_const_sub V B
    have hm := d.empiricalRow_upper_bennett_radius_strict W N hN B t hB ht hw
    rw [hv] at hm
    have hevent : {ω | r < (empiricalRow N hN ω).expectation W-d.expectation W} =
        {ω | r < -D ω} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      have h1 : (empiricalRow N hN ω).expectation W = B-(empiricalRow N hN ω).expectation V := by
        dsimp [W]
        rw [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_const]
      have h2 : d.expectation W = B-d.expectation V := by
        dsimp [W]
        rw [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_const]
      rw [h1, h2]
      dsimp [D]
      ring_nf
    rw [hevent] at hm
    let A : Set (Fin N → State) := {ω | r < |D ω|}
    let C : Set (Fin N → State) := {ω | Real.sqrt (d.variance V) >
      Real.sqrt ((N : ℝ)/((N : ℝ)-1)*empiricalVariance N hN V ω) +
        B*Real.sqrt (2*t/((N : ℝ)-1))}
    have hA : (d.sampleMeasure N).real A ≤ 2*Real.exp (-t) := by
      calc
        _ ≤ (d.sampleMeasure N).real ({ω | r < D ω} ∪ {ω | r < -D ω}) := by
          apply measureReal_mono ?_ (measure_ne_top _ _)
          intro ω hω
          change r < |D ω| at hω
          change r < D ω ∨ r < -D ω
          exact lt_abs.mp hω
        _ ≤ (d.sampleMeasure N).real {ω | r < D ω} +
            (d.sampleMeasure N).real {ω | r < -D ω} := measureReal_union_le _ _
        _ ≤ Real.exp (-t) + Real.exp (-t) := by
          have hp' : (d.sampleMeasure N).real {ω | r < D ω} ≤ Real.exp (-t) := hp
          exact add_le_add hp' hm
        _ = 2*Real.exp (-t) := by ring
    have hC : (d.sampleMeasure N).real C ≤ Real.exp (-t) :=
      d.empiricalStd_population_exceedance N hN2 V B t hBp ht hV
    have hsub : {ω : Fin N → State |
      Real.sqrt (2*empiricalVariance N hN V ω*t/((N : ℝ)-1)) +
          7*B*t/(3*((N : ℝ)-1)) < |D ω|} ⊆ A ∪ C := by
      intro ω hω
      by_cases hc : ω ∈ C
      · exact Or.inr hc
      · left
        have hstd : Real.sqrt (d.variance V) ≤
            Real.sqrt ((N : ℝ)/((N : ℝ)-1)*empiricalVariance N hN V ω) +
              B*Real.sqrt (2*t/((N : ℝ)-1)) := le_of_not_gt hc
        have halg := StatisticalRL.Probability.empirical_bernstein_sharp_radius_algebra
          (N : ℝ) B t (d.variance V) (empiricalVariance N hN V ω)
          hn hB ht.le (d.variance_nonneg V) (empiricalVariance_nonneg N hN V ω) hstd
        exact lt_of_le_of_lt halg hω
    calc
      _ ≤ (d.sampleMeasure N).real (A ∪ C) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (d.sampleMeasure N).real A+(d.sampleMeasure N).real C := measureReal_union_le _ _
      _ ≤ 3*Real.exp (-t) := by linarith

end StatisticalRL.FiniteDistribution

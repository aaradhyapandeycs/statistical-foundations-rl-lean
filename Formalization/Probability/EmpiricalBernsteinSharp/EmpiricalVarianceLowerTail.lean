import Formalization.Probability.EmpiricalBernsteinSharp.FiniteSelfBoundTail
import Formalization.Probability.EmpiricalBernsteinSharp.EmpiricalVarianceSelfBounding

/-! Private uncompiled lower-tail specialization for the actual normalized
unbiased empirical variance. -/
open scoped BigOperators
open MeasureTheory
namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance varianceLowerTailStateMeasurable : MeasurableSpace State := ⊤

theorem normalizedUnbiasedVariance_lower_tail (d : FiniteDistribution State)
    (N : ℕ) (hN2 : 2 ≤ N) (V : State → ℝ) (B t : ℝ)
    (hB : 0 < B) (ht : 0 < t) (hV : ∀ s, V s ∈ Set.Icc 0 B) :
    (d.sampleMeasure N).real {ω |
      Real.sqrt (2*((N : ℝ)/((N : ℝ)-1))*((N : ℝ)*d.variance V/B^2)*t) <
        (N : ℝ)*d.variance V/B^2 - normalizedUnbiasedVariance N hN2 V B ω} ≤
      Real.exp (-t) := by
  classical
  let f := normalizedUnbiasedVariance N hN2 V B
  let fi : Fin N → (Fin N → State) → ℝ := fun i ω ↦
    normalizedUnbiasedVarianceRemoved N hN2 V B ω i
  let a : ℝ := (N : ℝ)/((N : ℝ)-1)
  have hn : (1 : ℝ) < N := by
    have h : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < N-1)]
    linarith
  have hind (j : Fin N) (ω : Fin N → State) (s : State) :
      fi j (Function.update ω j s) = fi j ω := by
    apply normalizedUnbiasedVarianceRemoved_congr
    intro k hk
    exact Function.update_of_ne hk s ω
  have hdec (j : Fin N) (ω : Fin N → State) :
      0 ≤ f ω-fi j ω ∧ f ω-fi j ω ≤ 1 :=
    (normalizedUnbiasedVariance_decrements N hN2 V B hB hV ω).1 j
  have hsq (ω : Fin N → State) : (∑ j, (f ω-fi j ω)^2) ≤ a*f ω :=
    (normalizedUnbiasedVariance_decrements N hN2 V B hB hV ω).2
  have hmean : (∑ ω : Fin N → State, (∏ i, d.prob (ω i))*f ω) =
      (N : ℝ)*d.variance V/B^2 := by
    rw [← d.sampleMeasure_integral_product_mass]
    exact d.normalizedUnbiasedVariance_integral N hN2 V B hB
  have h := d.sampleMeasure_self_bound_lower_tail N f fi a t ha ht hind hdec hsq
  rw [hmean] at h
  exact h

end StatisticalRL.FiniteDistribution

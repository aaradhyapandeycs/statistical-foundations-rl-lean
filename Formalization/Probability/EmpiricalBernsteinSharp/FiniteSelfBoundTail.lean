import Formalization.Probability.EmpiricalBernsteinSharp.FiniteSelfBoundChernoff

/-! Private uncompiled sharp lower-tail consumer for the actual iid law. -/
open scoped BigOperators
open MeasureTheory
namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance finiteSelfBoundTailStateMeasurable : MeasurableSpace State := ⊤

theorem sampleMeasure_self_bound_lower_tail (d : FiniteDistribution State)
    (N : ℕ) (f : (Fin N → State) → ℝ)
    (fi : Fin N → (Fin N → State) → ℝ) (a t : ℝ)
    (ha : 1 ≤ a) (ht : 0 < t)
    (hind : ∀ j ω s, fi j (Function.update ω j s) = fi j ω)
    (hdec : ∀ j ω, 0 ≤ f ω-fi j ω ∧ f ω-fi j ω ≤ 1)
    (hsq : ∀ ω, (∑ j, (f ω-fi j ω)^2) ≤ a*f ω) :
    (d.sampleMeasure N).real {ω |
      Real.sqrt (2*a*(∑ ω', (∏ i, d.prob (ω' i))*f ω')*t) <
        (∑ ω', (∏ i, d.prob (ω' i))*f ω') - f ω} ≤ Real.exp (-t) := by
  classical
  let m : ℝ := ∑ ω' : Fin N → State, (∏ i, d.prob (ω' i))*f ω'
  have ha0 : 0 < a := by linarith
  have hf (ω : Fin N → State) : 0 ≤ f ω := by
    have hs : 0 ≤ ∑ j, (f ω-fi j ω)^2 := Finset.sum_nonneg (fun j hj ↦ sq_nonneg _)
    nlinarith [hsq ω]
  have hm : 0 ≤ m := Finset.sum_nonneg (fun ω hω ↦
    mul_nonneg (Finset.prod_nonneg (fun i hi ↦ d.prob_nonneg _)) (hf ω))
  by_cases hm0 : m = 0
  · have hempty : {ω : Fin N → State | Real.sqrt (2*a*m*t) < m-f ω} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [hm0]
      simp only [mul_zero, zero_mul, Real.sqrt_zero, zero_sub]
      exact not_lt_of_ge (neg_nonpos.mpr (hf ω))
    change (d.sampleMeasure N).real {ω | Real.sqrt (2*a*m*t) < m-f ω} ≤ Real.exp (-t)
    rw [hempty, measureReal_empty]
    positivity
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    let r : ℝ := Real.sqrt (2*a*m*t)
    let theta : ℝ := r/(a*m)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hrsq : r^2 = 2*a*m*t := Real.sq_sqrt (by positivity)
    have htheta : 0 ≤ theta := div_nonneg hr (mul_pos ha0 hmpos).le
    have hquad : -theta*r+a*m*theta^2/2 = -t := by
      dsimp [theta]
      field_simp [ne_of_gt ha0, ne_of_gt hmpos]
      nlinarith [hrsq]
    have hc := d.sampleMeasure_self_bound_chernoff N f fi a theta r ha htheta hind hdec hsq
    change (d.sampleMeasure N).real {ω | r < m-f ω} ≤ Real.exp (-t)
    calc
      _ ≤ (d.sampleMeasure N).real {ω | r ≤ m-f ω} := by
        apply measureReal_mono ?_ (measure_ne_top _ _)
        intro ω hω
        change r < m-f ω at hω
        exact le_of_lt hω
      _ ≤ Real.exp (-theta*r+a*m*theta^2/2) := hc
      _ = _ := by rw [hquad]

end StatisticalRL.FiniteDistribution

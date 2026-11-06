import Formalization.Probability.EmpiricalBernsteinSharp.FiniteSelfBoundMGF
import Formalization.Probability.EmpiricalBernsteinSharp.FiniteProductMeasure

/-! Private uncompiled Chernoff consumer for finite iid self-bounding
statistics. The variance-specific and family results remain separate. -/
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.FiniteDistribution

variable {State : Type*} [Fintype State]
local instance finiteSelfBoundChernoffStateMeasurable : MeasurableSpace State := ⊤

theorem sampleMeasure_self_bound_chernoff (d : FiniteDistribution State)
    (N : ℕ) (f : (Fin N → State) → ℝ)
    (fi : Fin N → (Fin N → State) → ℝ) (a theta r : ℝ)
    (ha : 1 ≤ a) (htheta : 0 ≤ theta)
    (hind : ∀ j ω s, fi j (Function.update ω j s) = fi j ω)
    (hdec : ∀ j ω, 0 ≤ f ω-fi j ω ∧ f ω-fi j ω ≤ 1)
    (hsq : ∀ ω, (∑ j, (f ω-fi j ω)^2) ≤ a*f ω) :
    (d.sampleMeasure N).real {ω |
      r ≤ (∑ ω', (∏ i, d.prob (ω' i))*f ω') - f ω} ≤
      Real.exp (-theta*r+a*(∑ ω', (∏ i, d.prob (ω' i))*f ω')*theta^2/2) := by
  classical
  let m : ℝ := ∑ ω' : Fin N → State, (∏ i, d.prob (ω' i))*f ω'
  have hmgf := StatisticalRL.EmpiricalBernsteinEntropy.finite_sample_self_bound_laplace
    State d.prob d.prob_nonneg d.sum_prob N f fi a theta ha htheta hind hdec hsq
  have hident : ProbabilityTheory.mgf (fun ω : Fin N → State ↦ -f ω)
      (d.sampleMeasure N) theta =
      StatisticalRL.EmpiricalBernsteinEntropy.finiteSampleLaplace d.prob N f theta := by
    unfold ProbabilityTheory.mgf
    rw [d.sampleMeasure_integral_product_mass]
    unfold StatisticalRL.EmpiricalBernsteinEntropy.finiteSampleLaplace
    apply Finset.sum_congr rfl
    intro ω hω
    have heq : theta * (-f ω) = -theta * f ω := by ring
    rw [heq]
  have hint : Integrable (fun ω : Fin N → State ↦ Real.exp (theta * (-f ω)))
      (d.sampleMeasure N) := Integrable.of_finite
  have h := ProbabilityTheory.measure_ge_le_exp_mul_mgf
    (X := fun ω : Fin N → State ↦ -f ω) (r-m) htheta hint
  rw [hident] at h
  have hevent : {ω : Fin N → State | r-m ≤ -f ω} = {ω | r ≤ m-f ω} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hω <;> linarith
  rw [hevent] at h
  change (d.sampleMeasure N).real {ω | r ≤ m-f ω} ≤ Real.exp (-theta*r+a*m*theta^2/2)
  calc
    _ ≤ Real.exp (-theta*(r-m)) *
        StatisticalRL.EmpiricalBernsteinEntropy.finiteSampleLaplace d.prob N f theta := h
    _ ≤ Real.exp (-theta*(r-m))*Real.exp (-theta*m+a*m*theta^2/2) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end StatisticalRL.FiniteDistribution

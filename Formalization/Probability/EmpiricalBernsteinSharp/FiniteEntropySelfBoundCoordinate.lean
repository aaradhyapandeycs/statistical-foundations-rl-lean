import Formalization.Probability.EmpiricalBernsteinSharp.FiniteEntropyVariational
import Formalization.Probability.EmpiricalBernsteinSharp.BennettPositiveRemainder

/-! Private uncompiled entropy-method coordinate estimate. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

/-- A positive exponential's one-coordinate entropy is controlled by the
squared decrement from a coordinate-independent lower comparator. -/
theorem finite_entropy_exp_decrement_le {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (c theta : ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (htheta : 0 ≤ theta) (hd0 : ∀ i, 0 ≤ f i - c) (hd1 : ∀ i, f i - c ≤ 1) :
    (∑ i, p i*(Real.exp (-theta*f i)*Real.log (Real.exp (-theta*f i)))) -
      (∑ i, p i*Real.exp (-theta*f i))*Real.log (∑ i, p i*Real.exp (-theta*f i)) ≤
      (Real.exp theta-1-theta) * ∑ i, p i*(Real.exp (-theta*f i)*(f i-c)^2) := by
  let g : ι → ℝ := fun i ↦ Real.exp (-theta*f i)
  let C : ℝ := Real.exp (-theta*c)
  have hg (i : ι) : 0 < g i := Real.exp_pos _
  have hC : 0 < C := Real.exp_pos _
  have hv := finite_entropy_le_relative_constant p g C hp hp1 hg hC
  have hpoint (i : ι) : g i*Real.log (g i/C)-g i+C ≤
      (Real.exp theta-1-theta)*(g i*(f i-c)^2) := by
    have hr := StatisticalRL.SharpBernstein.exp_remainder_scaled_nonnegative
      theta (f i-c) htheta (hd0 i) (hd1 i)
    have hlog : Real.log (g i/C) = -theta*(f i-c) := by
      dsimp [g, C]
      rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _)),
        Real.log_exp, Real.log_exp]
      ring
    have hexp : C = g i*Real.exp (theta*(f i-c)) := by
      dsimp [g, C]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hlog, hexp]
    have hmul := mul_le_mul_of_nonneg_left hr (hg i).le
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    mul_le_mul_of_nonneg_left (hpoint i) (hp i))
  have hfactor : (∑ i, p i*((Real.exp theta-1-theta)*(g i*(f i-c)^2))) =
      (Real.exp theta-1-theta) * ∑ i, p i*(g i*(f i-c)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfactor] at hsum
  exact hv.trans hsum

end StatisticalRL.EmpiricalBernsteinEntropy

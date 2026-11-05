import Formalization.Probability.AzumaExpStep
import Mathlib.Probability.Process.Filtration

/-! finite-horizon exponential-moment induction on arbitrary Ω.
The partial-sum measurability premise is an intermediate filtration fact. -/
namespace StatisticalRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem azuma_sum_mgf_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (B : ℕ → ℝ)
    (hX : ∀n, @Measurable Ω ℝ mΩ (inferInstance : MeasurableSpace ℝ) (X n))
    (hB : ∀n, 0≤B n) (hb : ∀n ω, |X n ω|≤B n)
    (hc : ∀n, μ[X n | ℱ n] =ᵐ[μ] 0)
    (hSm : ∀n, StronglyMeasurable[ℱ n] (fun ω => ∑ i ∈ Finset.range n, X i ω))
    (n : ℕ) (t : ℝ) :
    (∫ ω, Real.exp (t*(∑ i ∈ Finset.range n, X i ω)) ∂μ) ≤
      Real.exp (t^2*(∑ i ∈ Finset.range n, (B i)^2)/2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : ∀ω, |∑ i ∈ Finset.range n, X i ω| ≤ ∑ i ∈ Finset.range n, B i := by
      intro ω
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi => hb i ω))
    have hC : 0≤∑ i ∈ Finset.range n, B i := Finset.sum_nonneg (fun i hi => hB i)
    have hstep := azuma_exp_step μ (ℱ n) (ℱ.le n) (fun ω => ∑ i ∈ Finset.range n, X i ω) (X n)
      (hSm n) (hX n) (∑ i ∈ Finset.range n, B i) (B n) hC (hB n) hs (hb n) (hc n) t
    have hm := mul_le_mul_of_nonneg_left ih (Real.exp_pos (t^2*(B n)^2/2)).le
    have he : Real.exp (t^2*(B n)^2/2)*Real.exp (t^2*(∑ i ∈ Finset.range n, (B i)^2)/2) =
        Real.exp (t^2*(∑ i ∈ Finset.range (n+1), (B i)^2)/2) := by
      rw [← Real.exp_add, Finset.sum_range_succ]
      congr 1
      ring
    calc
      _ = (∫ ω, Real.exp (t*((∑ i ∈ Finset.range n, X i ω)+X n ω)) ∂μ) := by simp only [Finset.sum_range_succ]
      _ ≤ Real.exp (t^2*(B n)^2/2)*(∫ ω, Real.exp (t*(∑ i ∈ Finset.range n, X i ω)) ∂μ) := hstep
      _ ≤ _ := hm.trans_eq he
end StatisticalRL

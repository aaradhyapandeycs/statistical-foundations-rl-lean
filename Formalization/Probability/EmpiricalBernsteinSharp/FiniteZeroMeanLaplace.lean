import Formalization.Probability.EmpiricalBernsteinSharp.FiniteSelfBoundLogMGF

/-! Private uncompiled zero-mean branch for finite nonnegative statistics. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

theorem finite_sample_laplace_eq_one_of_zero_mean {State : Type*} [Fintype State]
    (p : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (n : ℕ) (f : (Fin n → State) → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    (hmean : (∑ ω, (∏ i, p (ω i))*f ω) = 0) (theta : ℝ) :
    finiteSampleLaplace p n f theta = 1 := by
  classical
  have hw (ω : Fin n → State) : 0 ≤ ∏ i, p (ω i) :=
    Finset.prod_nonneg (fun i hi ↦ hp _)
  have hzero (ω : Fin n → State) : (∏ i, p (ω i))*f ω = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun ω (_ : ω ∈ Finset.univ) ↦ mul_nonneg (hw ω) (hf ω))).mp hmean
    exact h ω (Finset.mem_univ _)
  unfold finiteSampleLaplace
  calc
    _ = ∑ ω : Fin n → State, ∏ i, p (ω i) := by
      apply Finset.sum_congr rfl
      intro ω hω
      rcases mul_eq_zero.mp (hzero ω) with hz | hz
      · simp [hz]
      · simp [hz]
    _ = 1 := finite_sample_product_mass_sum p hp1 n

end StatisticalRL.EmpiricalBernsteinEntropy

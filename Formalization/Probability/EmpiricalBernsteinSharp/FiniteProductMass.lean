import Formalization.Probability.EmpiricalBernsteinSharp.FiniteProductSplit

/-! Private uncompiled finite iid product-mass normalization. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

theorem finite_sample_product_mass_sum {State : Type*} [Fintype State]
    (p : State → ℝ) (hp1 : ∑ s, p s = 1) (n : ℕ) :
    (∑ ω : Fin n → State, ∏ i : Fin n, p (ω i)) = 1 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finite_sample_sum_head_tail]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      simp only [← Finset.mul_sum, ih, mul_one, hp1]

end StatisticalRL.EmpiricalBernsteinEntropy

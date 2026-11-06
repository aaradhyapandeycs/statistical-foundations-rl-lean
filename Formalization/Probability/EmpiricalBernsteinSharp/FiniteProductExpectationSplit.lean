import Formalization.Probability.EmpiricalBernsteinSharp.FiniteProductMass

/-! Private uncompiled weighted head/tail expansion for finite iid samples. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

theorem finite_sample_product_expectation_head_tail {State : Type*} [Fintype State]
    (p : State → ℝ) (n : ℕ) (F : (Fin (n+1) → State) → ℝ) :
    (∑ ω, (∏ i : Fin (n+1), p (ω i)) * F ω) =
      ∑ s : State, p s * ∑ tail : Fin n → State,
        (∏ i : Fin n, p (tail i)) * F (Fin.cons s tail) := by
  classical
  rw [finite_sample_sum_head_tail]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail htail
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

end StatisticalRL.EmpiricalBernsteinEntropy

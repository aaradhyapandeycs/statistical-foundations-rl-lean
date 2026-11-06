import Formalization.Probability.EmpiricalBernsteinSharp.FiniteProductExpectationSplit

/-! Private uncompiled head-coordinate entropy identity for iid samples. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

theorem finite_sample_head_coordinate_entropy {State : Type*} [Fintype State]
    (p : State → ℝ) (n : ℕ) (F : (Fin (n+1) → State) → ℝ) :
    (∑ ω : Fin (n+1) → State, (∏ i, p (ω i)) *
      (F ω * Real.log (F ω / ∑ s, p s * F (Function.update ω 0 s)))) =
    ∑ tail : Fin n → State, (∏ i, p (tail i)) *
      ∑ s : State, p s * (F (Fin.cons s tail) *
        Real.log (F (Fin.cons s tail) / ∑ z, p z * F (Fin.cons z tail))) := by
  classical
  rw [finite_sample_product_expectation_head_tail]
  simp only [Fin.update_cons_zero]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tail htail
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem finite_sample_tail_coordinate_entropy {State : Type*} [Fintype State]
    (p : State → ℝ) (n : ℕ) (F : (Fin (n+1) → State) → ℝ) (j : Fin n) :
    (∑ ω : Fin (n+1) → State, (∏ i, p (ω i)) *
      (F ω * Real.log (F ω / ∑ s, p s * F (Function.update ω j.succ s)))) =
    ∑ head : State, p head * ∑ tail : Fin n → State, (∏ i, p (tail i)) *
      (F (Fin.cons head tail) * Real.log (F (Fin.cons head tail) /
        ∑ s, p s * F (Fin.cons head (Function.update tail j s)))) := by
  classical
  rw [finite_sample_product_expectation_head_tail]
  simp only [← Fin.cons_update]

end StatisticalRL.EmpiricalBernsteinEntropy

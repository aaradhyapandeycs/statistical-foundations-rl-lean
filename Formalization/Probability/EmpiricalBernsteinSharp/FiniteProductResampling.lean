import Formalization.Probability.EmpiricalBernsteinSharp.FiniteProductExpectationSplit

/-! Private uncompiled resampling invariance for finite iid product weights. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

/-- Averaging a fresh draw into one chosen coordinate preserves every finite
product expectation. -/
theorem finite_sample_resampling_invariant {State : Type*} [Fintype State]
    (p : State → ℝ) (hp1 : ∑ s, p s = 1) (n : ℕ)
    (F : (Fin n → State) → ℝ) (j : Fin n) :
    (∑ ω : Fin n → State, (∏ i, p (ω i)) *
      (∑ s, p s * F (Function.update ω j s))) =
      ∑ ω : Fin n → State, (∏ i, p (ω i)) * F ω := by
  classical
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [finite_sample_product_expectation_head_tail,
        finite_sample_product_expectation_head_tail]
      cases j using Fin.cases with
      | zero =>
          simp only [Fin.update_cons_zero]
          rw [← Finset.sum_mul, hp1, one_mul]
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro tail ht
          ring
      | succ j =>
          simp only [← Fin.cons_update]
          apply Finset.sum_congr rfl
          intro head hh
          congr 1
          exact ih (fun tail ↦ F (Fin.cons head tail)) j

end StatisticalRL.EmpiricalBernsteinEntropy

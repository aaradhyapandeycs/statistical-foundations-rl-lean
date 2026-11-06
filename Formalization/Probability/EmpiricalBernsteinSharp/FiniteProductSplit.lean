import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

/-! Private finite sample-coordinate split for the tensorization induction. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

theorem finite_sample_sum_head_tail {State : Type*} [Fintype State]
    (n : ℕ) (F : (Fin (n+1) → State) → ℝ) :
    (∑ ω, F ω) = ∑ s : State, ∑ tail : Fin n → State, F (Fin.cons s tail) := by
  classical
  calc
    _ = ∑ pair : State × (Fin n → State), F (Fin.cons pair.1 pair.2) := by
      exact ((Fin.consEquiv (fun _ : Fin (n+1) ↦ State)).sum_comp F).symm
    _ = _ := by rw [Fintype.sum_prod_type]

end StatisticalRL.EmpiricalBernsteinEntropy

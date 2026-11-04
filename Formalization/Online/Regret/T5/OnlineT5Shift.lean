import Formalization.Online.Regret.T5.OnlineT5Scalar

/-! Actual-law variance and gap proof component: OnlineT5Shift.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem onlineT5_square_shift_le (H : ℕ) (v m : ℕ → ℝ) (hterminal : v H = 0) :
    (∑ n ∈ Finset.range H, ((v (n + 1))^2 - (m n)^2)) ≤
      ∑ n ∈ Finset.range H, ((v n)^2 - (m n)^2) := by
  have hs : (∑ n ∈ Finset.range H, (v (n + 1))^2) + (v 0)^2 =
      (∑ n ∈ Finset.range H, (v n)^2) + (v H)^2 := by
    have h1 := Finset.sum_range_succ' (fun n => (v n)^2) H
    have h2 := Finset.sum_range_succ (fun n => (v n)^2) H
    linarith
  have h0 := sq_nonneg (v 0)
  simp only [Finset.sum_sub_distrib]
  rw [hterminal] at hs
  nlinarith
end StatisticalRL.OnlineRL

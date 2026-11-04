import Formalization.Probability.EmpiricalBernstein

/-! Fixed bounded value: the variance of its square is controlled by its
original variance. This is a deterministic prerequisite for W₃. -/
namespace StatisticalRL.OnlineRL
variable {State : Type*} [Fintype State]

theorem onlineW3_square_variance_le
    (p : FiniteDistribution State) (V : State → ℝ) (H : ℝ)
    (hH : 0 ≤ H) (hV : ∀ s, 0 ≤ V s ∧ V s ≤ H) :
    p.variance (fun s => (V s)^2) ≤ 4 * H^2 * p.variance V := by
  let m := p.expectation V
  have hm0 : 0 ≤ m := p.expectation_nonneg (fun s => (hV s).1)
  have hmH : m ≤ H := p.expectation_le_const (fun s => (hV s).2)
  have hv := p.variance_le_expectation_sq (fun s => m^2 - (V s)^2)
  rw [p.variance_const_sub (fun s => (V s)^2) (m^2)] at hv
  apply hv.trans
  have hpoint (s : State) : (m^2 - (V s)^2)^2 ≤ 4 * H^2 * (V s - m)^2 := by
    have hx : 0 ≤ V s + m := by linarith [(hV s).1]
    have hy : V s + m ≤ 2 * H := by linarith [(hV s).2]
    have hsq : (V s + m)^2 ≤ (2 * H)^2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg (V s - m))
    nlinarith [hmul]
  have h := p.expectation_mono hpoint
  rw [show (fun s => 4 * H^2 * (V s - m)^2) =
      (fun s => (4 * H^2) * (V s - m)^2) by rfl, p.expectation_mul] at h
  rw [p.variance_eq_expectation_centered_sq]
  exact h
end StatisticalRL.OnlineRL

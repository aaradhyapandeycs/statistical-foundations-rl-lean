import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Exact logarithm of the finite profile/choice/level/mask union budget. -/
namespace StatisticalRL.OnlineRL

theorem mvp_unionLog_decompose (P J p δ K : ℝ) (d : ℕ)
    (hP : 0 < P) (hJ : 0 < J) (hp : 0 < p) (hδ : 0 < δ) (hK : 0 < K) :
    Real.log (2*p*(P*(K+1)^d*J*2^d)/δ) =
      Real.log P + (d : ℝ)*Real.log (K+1) + Real.log J +
        (d : ℝ)*Real.log 2 + Real.log (2*p) + Real.log (1/δ) := by
  have hK1 : K+1 ≠ 0 := by linarith
  have hN : P*(K+1)^d*J*(2:ℝ)^d ≠ 0 := by positivity
  rw [Real.log_div (mul_ne_zero (by positivity) hN) (ne_of_gt hδ),
    Real.log_mul (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hp)) hN,
    Real.log_mul (mul_ne_zero (mul_ne_zero (ne_of_gt hP) (pow_ne_zero _ hK1)) (ne_of_gt hJ)) (by positivity),
    Real.log_mul (mul_ne_zero (ne_of_gt hP) (pow_ne_zero _ hK1)) (ne_of_gt hJ),
    Real.log_mul (ne_of_gt hP) (pow_ne_zero _ hK1),
    Real.log_pow, Real.log_pow, Real.log_div (by norm_num : (1:ℝ) ≠ 0) (ne_of_gt hδ)]
  simp only [Real.log_one, zero_sub]
  ring
end StatisticalRL.OnlineRL

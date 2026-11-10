import Formalization.Online.Regret.Algebra.OnlineT234ConfidenceAlgebra
import Mathlib.Data.Nat.Log

/-! Same-experiment suffix proof component: OnlineT56ConfidenceAlgebra.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL

theorem onlineT56_two_natLog2_le (N : ℕ) : 2 * Nat.log2 N ≤ N := by
  have hpow (m : ℕ) : 2 * m ≤ 2^m := by
    have hs : ∀ n : ℕ, 2 * (n + 1) ≤ 2^(n + 1) := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [pow_succ]
        have hm := Nat.mul_le_mul_left 2 ih
        omega
    cases m with
    | zero => norm_num
    | succ n => exact hs n
  by_cases hN : N = 0
  · subst N; decide
  · have hp := Nat.pow_log_le_self 2 hN
    rw [← Nat.log2_eq_log_two] at hp
    exact (hpow _).trans hp

theorem onlineT56_realLog2_le (N : ℕ) (hN : 0 < N) :
    Real.log N / Real.log 2 ≤ (N : ℝ) := by
  have ht : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ ht).mpr
  have hp : (N : ℝ) ≤ (2 : ℝ)^N := by
    exact_mod_cast (show N ≤ 2^N from Nat.lt_two_pow_self.le)
  have hlog := Real.log_le_log (by exact_mod_cast hN : (0 : ℝ) < N) hp
  simpa only [Real.log_pow] using hlog

/-- The shared W12 and suffix martingale families fit the source J2 budget
when S≥2. The one-state case is a separate actual-path obligation. -/
theorem onlineT56_suffix_family_failure_le_nine
    (S A H K : ℝ) (l : ℝ)
    (hS : 2 ≤ S) (hA : 1 ≤ A) (hH : 1 ≤ H) (hK : 1 ≤ K)
    (hl : l ≤ K * H) :
    (4 * S + 6) * S * A * H * K + 4 * H * l ≤ 9 * S^2 * A * H^2 * K := by
  have hS0 : 0 ≤ S := by linarith only [hS]
  have hA0 : 0 ≤ A := by linarith only [hA]
  have hH0 : 0 ≤ H := by linarith only [hH]
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hcoef : 4 * S^2 + 6 * S + 4 ≤ 9 * S^2 := by
    nlinarith only [hS, sq_nonneg (S - 2)]
  have hbase : (4 * S + 6) * S * A * H * K ≤
      (4 * S + 6) * S * A * H^2 * K := by
    have hm := mul_le_mul_of_nonneg_left hH
      (show 0 ≤ (4 * S + 6) * S * A * H * K by positivity)
    nlinarith only [hm]
  have hlog : 4 * H * l ≤ 4 * A * H^2 * K := by
    have h1 := mul_le_mul_of_nonneg_left hl (show 0 ≤ 4 * H by positivity)
    have h2 := mul_le_mul_of_nonneg_right hA (show 0 ≤ 4 * H^2 * K by positivity)
    nlinarith only [h1,h2]
  have h3 := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ A * H^2 * K by positivity)
  nlinarith only [hbase,hlog,h3]

end StatisticalRL.OnlineRL

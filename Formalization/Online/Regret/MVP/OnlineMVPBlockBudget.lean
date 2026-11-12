import Formalization.Online.Regret.MVP.OnlineMVPStoredCount
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! MVP count and deterministic visit-budget results. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- A full dyadic block [2^j,2^(j+1)) with the preceding batch size
2^(j-1) has reciprocal mass exactly two. -/
theorem onlineMVP_full_dyadic_block_mass (j : ℕ) (hj : 1 ≤ j) :
    (∑ _n ∈ Finset.Ico (2^j) (2^(j+1)), (1 : ℝ) / (2^(j-1) : ℕ)) = 2 := by
  have hcard : (Finset.Ico (2^j) (2^(j+1))).card = 2^j := by
    simp only [Nat.card_Ico, Nat.pow_succ]
    omega
  have hpow : (2^j : ℕ) = 2 * 2^(j-1) := by
    have he : j = (j - 1) + 1 := by omega
    conv_lhs => rw [he, Nat.pow_succ]
    omega
  simp only [Finset.sum_const, hcard, nsmul_eq_mul]
  rw [hpow]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hp : (0 : ℝ) < (2 : ℝ)^(j-1) := by positivity
  field_simp
  <;> ring

end StatisticalRL.OnlineRL

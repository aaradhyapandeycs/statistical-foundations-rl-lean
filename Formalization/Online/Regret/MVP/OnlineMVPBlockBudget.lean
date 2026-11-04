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

/-- The first nonempty batch causes at most four units of reciprocal mass;
its zero-count convention is included in these four terms. -/
theorem onlineMVP_first_four_reciprocals :
    (∑ n ∈ Finset.range 4, (1 : ℝ) / max (onlineMVPStoredCount n) 1) = 4 := by
  have h0 : onlineMVPStoredCount 0 = 0 := by decide
  have h1 : onlineMVPStoredCount 1 = 1 := by decide
  have h2 : onlineMVPStoredCount 2 = 1 := by decide
  have h3 : onlineMVPStoredCount 3 = 1 := by decide
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3]
end StatisticalRL.OnlineRL

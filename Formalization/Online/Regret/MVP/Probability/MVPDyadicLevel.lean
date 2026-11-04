import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Exact noninitial source batch levels as finite indices. -/
namespace StatisticalRL.OnlineRL

def mvpUniformLevel (K : ℕ) := Fin (Nat.log2 K)

def mvpUniformBatchSize {K : ℕ} (l : mvpUniformLevel K) : ℕ := 2 ^ l.val

theorem mvpUniformBatchSize_pos {K : ℕ} (l : mvpUniformLevel K) :
    0 < mvpUniformBatchSize l := by
  unfold mvpUniformBatchSize
  positivity

theorem mvpUniformBatchSize_fits {K : ℕ} (hK : 2 ≤ K) (l : mvpUniformLevel K) :
    2 * mvpUniformBatchSize l ≤ K := by
  have hpow : 2 ^ (l.val + 1) ≤ 2 ^ Nat.log2 K :=
    Nat.pow_le_pow_right (by decide) (by exact l.isLt)
  have hbase : 2 ^ Nat.log2 K ≤ K := Nat.log2_self_le (by omega)
  calc
    2 * mvpUniformBatchSize l = 2 ^ (l.val + 1) := by simp [mvpUniformBatchSize, pow_succ, Nat.mul_comm]
    _ ≤ 2 ^ Nat.log2 K := hpow
    _ ≤ K := hbase
end StatisticalRL.OnlineRL

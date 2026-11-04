import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-! A deterministic offset slice for one positive-length MVP batch. -/
namespace StatisticalRL.OnlineRL

def mvpBatchIndex (K n : ℕ) (h : 2*n ≤ K) (i : Fin n) : Fin K :=
  ⟨n+i.val, by omega⟩

theorem mvpBatchIndex_injective (K n : ℕ) (h : 2*n ≤ K) :
    Function.Injective (mvpBatchIndex K n h) := by
  intro i j hij
  apply Fin.ext
  have heq := congrArg Fin.val hij
  dsimp [mvpBatchIndex] at heq
  omega
end StatisticalRL.OnlineRL

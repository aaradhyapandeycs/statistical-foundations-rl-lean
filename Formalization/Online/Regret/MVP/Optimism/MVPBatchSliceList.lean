import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

/-! The committed source batch is the deterministic [n,2n) list slice. -/
namespace StatisticalRL.OnlineRL

theorem mvp_takeDropBatch_length {α : Type*} (xs : List α) (n : ℕ)
    (hn : 2*n ≤ xs.length) : ((xs.take (2*n)).drop n).length = n := by
  simp only [List.length_drop, List.length_take, Nat.min_eq_left hn]
  omega

theorem mvp_takeDropBatch_get {α : Type*} (xs : List α) (n : ℕ)
    (hn : 2*n ≤ xs.length) (j : Fin n) :
    ((xs.take (2*n)).drop n).get ⟨j.val, by rw [mvp_takeDropBatch_length xs n hn]; exact j.isLt⟩ =
      xs.get ⟨n+j.val, by omega⟩ := by
  simp [List.get_eq_getElem, List.getElem_drop, List.getElem_take]
end StatisticalRL.OnlineRL

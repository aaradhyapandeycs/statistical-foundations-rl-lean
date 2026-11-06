import Formalization.Online.QLearning.ActualBlock

/-! identity connecting the constructed block to the actual
sequential transcript; no probabilistic certificate is introduced. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- A finite list block decomposes around its actual h-th record. -/
theorem qLearning_listBlock_split {α : Type*} (xs : List α) (H h : ℕ)
    (hh : h < H) (hH : H ≤ xs.length) :
    xs.take H = xs.take h ++ [xs.get ⟨h, lt_of_lt_of_le hh hH⟩] ++
      (xs.drop (h+1)).take (H-(h+1)) := by
  have hdecomp : H = h + 1 + (H-(h+1)) := by omega
  conv_lhs => rw [hdecomp, List.take_add, List.take_add]
  rw [List.take_one_drop_eq_of_lt_length (lt_of_lt_of_le hh hH)]

/-- The constructed stage block is exactly the actual episode slice. -/
theorem qLearningActualBlock_eq_slice {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (h : Fin H) :
    qLearningActualBlock hH E bonus initial fallback path k h =
      ((qLearningActualSequentialHistory hH E bonus initial fallback path).drop (k.val*H)).take H := by
  classical
  let history := qLearningActualSequentialHistory hH E bonus initial fallback path
  let xs := history.drop (k.val*H)
  have hlen : history.length = K*H := by
    simp [history, qLearningActualSequentialHistory, onlineSequentialPathHistory_length]
  have hk : (k.val+1)*H ≤ K*H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  have hxs : H ≤ xs.length := by
    simp only [xs, List.length_drop, hlen]
    have he : (k.val+1)*H = k.val*H+H := by ring
    omega
  have hs := qLearning_listBlock_split xs H h.val h.isLt hxs
  have hj : k.val*H+h.val < history.length := by
    rw [hlen]
    have he : (k.val+1)*H = k.val*H+H := by ring
    have hh := h.isLt
    omega
  have hget : xs.get ⟨h.val, lt_of_lt_of_le h.isLt hxs⟩ =
      history.get ⟨k.val*H+h.val,hj⟩ := by
    simp [xs, List.get_eq_getElem, List.getElem_drop]
  simpa [qLearningActualBlock, qLearningActualBlockBefore, qLearningActualBlockAfter,
    qLearningActualBlockRecord, history, xs, hget, List.drop_drop, Nat.add_assoc] using hs.symm

end StatisticalRL.OnlineRL

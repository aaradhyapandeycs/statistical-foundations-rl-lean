import Formalization.Online.Regret.MVP.OnlineMVPStoredCount
import Mathlib.Tactic.Positivity

/-! MVP count and deterministic visit-budget results. -/
namespace StatisticalRL.OnlineRL

theorem onlineMVP_floorPower_le (n : ℕ) (hn : n ≠ 0) :
    2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn

theorem onlineMVP_lt_nextFloorPower (n : ℕ) :
    n < 2 ^ (Nat.log2 n + 1) := by
  rw [Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) n

theorem onlineMVP_log2_eq_of_dyadic_bounds (n j : ℕ)
    (hlo : 2^j ≤ n) (hhi : n < 2^(j+1)) : Nat.log2 n = j := by
  rw [Nat.log2_eq_log_two]
  exact Nat.log_eq_of_pow_le_of_lt_pow hlo hhi

theorem onlineMVP_trigger_power (j : ℕ) : onlineMVPRowTrigger (2^j) := by
  unfold onlineMVPRowTrigger
  constructor
  · positivity
  · simp only [Nat.log2_two_pow]

/-- The decidable trigger predicate is exactly membership in the positive
powers of two, independent of the floor-log implementation. -/
theorem onlineMVP_trigger_iff_power (n : ℕ) :
    onlineMVPRowTrigger n ↔ ∃ j : ℕ, n = 2^j := by
  constructor
  · intro h
    exact ⟨Nat.log2 n, h.2⟩
  · rintro ⟨j, rfl⟩
    exact onlineMVP_trigger_power j

theorem onlineMVP_no_trigger_between_powers (n j : ℕ)
    (hlo : 2^j < n) (hhi : n < 2^(j+1)) : ¬ onlineMVPRowTrigger n := by
  have hlog := onlineMVP_log2_eq_of_dyadic_bounds n j (Nat.le_of_lt hlo) hhi
  intro ht
  have hp := ht.2
  rw [hlog] at hp
  omega

/-- Between two triggers, the stored batch is fixed and pending visits
accumulate. This is a deterministic row-local statement. -/
theorem onlineMVP_no_trigger_run (n t : ℕ)
    (h : ∀ i < t, ¬ onlineMVPRowTrigger (n+i+1)) :
    onlineMVPRowCountState (n+t) =
      ((onlineMVPRowCountState n).1 + t, (onlineMVPRowCountState n).2) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hp : ∀ i < t, ¬ onlineMVPRowTrigger (n+i+1) := by
      intro i hi
      exact h i (by omega)
    have hnext := h t (by omega)
    have hi := ih hp
    rw [show n + (t + 1) = (n+t)+1 by omega]
    simp only [onlineMVPRowCountState, hnext, if_false, hi]
    congr 1 <;> omega

/-- At a trigger the pending batch, including the current visit, becomes
the stored batch and the pending counter resets. -/
theorem onlineMVP_state_at_trigger (n : ℕ)
    (h : onlineMVPRowTrigger (n+1)) :
    onlineMVPRowCountState (n+1) = (0, (onlineMVPRowCountState n).1 + 1) := by
  simp only [onlineMVPRowCountState, h, if_true]
end StatisticalRL.OnlineRL

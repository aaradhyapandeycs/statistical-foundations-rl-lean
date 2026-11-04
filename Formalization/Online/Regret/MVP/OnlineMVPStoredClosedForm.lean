import Formalization.Online.Regret.MVP.OnlineMVPDyadicTrigger

/-! MVP count and deterministic visit-budget results. -/
namespace StatisticalRL.OnlineRL

theorem onlineMVP_state_at_power_succ (j : ℕ) :
    onlineMVPRowCountState (2^(j+1)) = (0, 2^j) := by
  induction j with
  | zero => decide
  | succ j ih =>
    let p : ℕ := 2^(j+1)
    have hp : 0 < p := by dsimp [p]; positivity
    have hnext : 2^((j+1)+1) = p + p := by
      dsimp [p]
      rw [Nat.pow_succ]
      omega
    have hnoupdate : ∀ i < p-1, ¬ onlineMVPRowTrigger (p+i+1) := by
      intro i hi
      apply onlineMVP_no_trigger_between_powers (p+i+1) (j+1)
      · dsimp [p]; omega
      · rw [hnext]; omega
    have hrun := onlineMVP_no_trigger_run p (p-1) hnoupdate
    have hstart : onlineMVPRowCountState p = (0, 2^j) := by
      dsimp [p]
      exact ih
    rw [hstart] at hrun
    have htarget : onlineMVPRowTrigger (p+(p-1)+1) := by
      have heq : p+(p-1)+1 = 2^((j+1)+1) := by rw [hnext]; omega
      rw [heq]
      exact onlineMVP_trigger_power _
    have hfinal := onlineMVP_state_at_trigger (p+(p-1)) htarget
    rw [hrun] at hfinal
    have hidx : 2^((j+1)+1) = p+(p-1)+1 := by rw [hnext]; omega
    rw [hidx, hfinal]
    simp only
    congr 1 <;> omega

/-- Closed form for the actual stored row batch after n visits. The batch
is the preceding dyadic block length, not the largest total-count power. -/
theorem onlineMVP_storedCount_closedForm (n : ℕ) :
    onlineMVPStoredCount n = if n < 2 then n else 2^(Nat.log2 n - 1) := by
  by_cases hn : n < 2
  · have hc : n = 0 ∨ n = 1 := by omega
    rcases hc with rfl | rfl <;> decide
  · have hn0 : n ≠ 0 := by omega
    let m := Nat.log2 n
    have hm : 1 ≤ m := by
      dsimp [m]
      apply (Nat.le_log2 hn0).2
      simpa using (show 2 ≤ n by omega)
    have hp : 2^m ≤ n := by dsimp [m]; exact onlineMVP_floorPower_le n hn0
    have hnext : n < 2^(m+1) := by dsimp [m]; exact onlineMVP_lt_nextFloorPower n
    have hnoupdate : ∀ i < n - 2^m, ¬ onlineMVPRowTrigger (2^m+i+1) := by
      intro i hi
      apply onlineMVP_no_trigger_between_powers (2^m+i+1) m
      · omega
      · omega
    have hrun := onlineMVP_no_trigger_run (2^m) (n-2^m) hnoupdate
    have hstart : onlineMVPRowCountState (2^m) = (0, 2^(m-1)) := by
      have he : m = (m-1)+1 := by omega
      conv_lhs => rw [he]
      exact onlineMVP_state_at_power_succ (m-1)
    rw [hstart] at hrun
    have heq : n = 2^m + (n-2^m) := by omega
    have hs : (onlineMVPRowCountState n).2 = 2^(m-1) := by
      rw [heq, hrun]
    rw [if_neg hn]
    simpa [onlineMVPStoredCount, m] using hs
end StatisticalRL.OnlineRL

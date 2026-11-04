import Formalization.Online.Regret.MVP.OnlineMVPStoredCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! MVP count and deterministic visit-budget results. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- Incrementing one successor counter increases the row's batch mass by
exactly one, including when the outcome type has other possible states. -/
theorem onlineMVP_pendingAfter_sum {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (pending : Outcome → ℕ) (x : Outcome) :
    (∑ y : Outcome, (pending y + if y = x then 1 else 0)) = (∑ y : Outcome, pending y) + 1 := by
  rw [Finset.sum_add_distrib]
  have hs : (∑ y : Outcome, if y = x then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y hy hyx
      simp [hyx]
    · simp
  rw [hs]

/-- Exact operational invariant: at every time and row, total visits equal
its prefix count, while pending and stored counters equal the row-local
power-trigger recurrence indexed by that same prefix count. -/
theorem onlineMVPCountTablesRun_row_invariant {Row Outcome : Type*}
    [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) (n : ℕ) (r : Row) :
    let st := onlineMVPCountTablesRun rowAt nextAt n
    st.total r = onlineVisitCount rowAt n r ∧
    (∑ y : Outcome, st.pending r y) = (onlineMVPRowCountState (onlineVisitCount rowAt n r)).1 ∧
    st.stored r = onlineMVPStoredCount (onlineVisitCount rowAt n r) := by
  induction n with
  | zero => simp [onlineMVPCountTablesRun, onlineMVPCountTablesInit, onlineVisitCount_zero,
      onlineMVPRowCountState, onlineMVPStoredCount]
  | succ n ih =>
    by_cases hr : rowAt n = r
    · subst r
      have htotal := ih.1
      have hpending := ih.2.1
      have hstored := ih.2.2
      rw [onlineVisitCount_succ]
      simp only [if_pos rfl]
      by_cases ht : onlineMVPRowTrigger (onlineVisitCount rowAt n (rowAt n) + 1)
      · simp [onlineMVPCountTablesRun, onlineMVPCountTablesStep, Function.update_self,
          htotal, ht, onlineMVPRowCountState, onlineMVPStoredCount, onlineMVP_pendingAfter_sum,
          hpending]
      · simp [onlineMVPCountTablesRun, onlineMVPCountTablesStep, Function.update_self,
          htotal, ht, onlineMVPRowCountState, onlineMVPStoredCount, onlineMVP_pendingAfter_sum,
          hpending, hstored]
    · rw [onlineVisitCount_succ]
      by_cases ht : onlineMVPRowTrigger ((onlineMVPCountTablesRun rowAt nextAt n).total (rowAt n) + 1)
      · simp [onlineMVPCountTablesRun, onlineMVPCountTablesStep, Function.update_of_ne,
          hr, Ne.symm hr, ht, ih]
      · simp [onlineMVPCountTablesRun, onlineMVPCountTablesStep, Function.update_of_ne,
          hr, Ne.symm hr, ht, ih]
end StatisticalRL.OnlineRL

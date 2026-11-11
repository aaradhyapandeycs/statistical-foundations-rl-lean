import Formalization.Online.Regret.MVP.MVPModelDefinitions
import Formalization.Online.Regret.MVP.Model.OnlineMVPCommittedHistogram
import Formalization.Online.SourceOptimism.SuccessorStackPrefix
import Formalization.Online.SourceOptimism.VisitCountFoundation
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Private pathwise bridge from the retained histogram to the chronological
list of outcomes observed at one row. The source's dyadic interval and the
empirical-kernel normalization are developed separately below. -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators

variable {Row Outcome : Type*} [DecidableEq Row] [DecidableEq Outcome]

theorem onlineMVPRowVisitList_succ (rowAt : ℕ → Row) (nextAt : ℕ → Outcome)
    (n : ℕ) (r : Row) :
    onlineMVPRowVisitList rowAt nextAt (n + 1) r =
      onlineMVPRowVisitList rowAt nextAt n r ++
        (if rowAt n = r then [nextAt n] else []) := by
  unfold onlineMVPRowVisitList
  rw [List.range_succ, List.filterMap_append]
  have hlast : List.filterMap (fun t => if rowAt t = r then some (nextAt t) else none)
      [n] = (if rowAt n = r then [nextAt n] else []) := by
    by_cases h : rowAt n = r <;> simp [List.filterMap, h]
  rw [hlast]

/-- A row-local copy of the four pieces of information needed to describe
pending and committed batches. -/
structure OnlineMVPRowBatchState (Outcome : Type*) where
  total : ℕ
  pending : Outcome → ℕ
  stored : ℕ
  committed : Outcome → ℕ

def onlineMVPCommittedRowView [Fintype Outcome]
    (st : OnlineMVPCommittedTables Row Outcome) (r : Row) :
    OnlineMVPRowBatchState Outcome :=
  ⟨st.base.total r, st.base.pending r, st.base.stored r, st.committed r⟩

def onlineMVPRowBatchStateInit (Outcome : Type*) : OnlineMVPRowBatchState Outcome :=
  ⟨0, fun _ => 0, 0, fun _ => 0⟩

def onlineMVPRowBatchStateStep [Fintype Outcome] [DecidableEq Outcome]
    (st : OnlineMVPRowBatchState Outcome) (x : Outcome) :
    OnlineMVPRowBatchState Outcome := by
  let pendingAfter := fun y => st.pending y + if y = x then 1 else 0
  let totalAfter := st.total + 1
  if h : onlineMVPRowTrigger totalAfter then
    exact ⟨totalAfter, fun _ => 0, ∑ y, pendingAfter y, pendingAfter⟩
  else
    exact ⟨totalAfter, pendingAfter, st.stored, st.committed⟩

def onlineMVPRowBatchStateRun [Fintype Outcome] [DecidableEq Outcome]
    (xs : List Outcome) : OnlineMVPRowBatchState Outcome :=
  xs.foldl onlineMVPRowBatchStateStep (onlineMVPRowBatchStateInit Outcome)

theorem onlineMVPRowBatchStateRun_append_one [Fintype Outcome] [DecidableEq Outcome]
    (xs : List Outcome) (x : Outcome) :
    onlineMVPRowBatchStateRun (xs ++ [x]) =
      onlineMVPRowBatchStateStep (onlineMVPRowBatchStateRun xs) x := by
  simp [onlineMVPRowBatchStateRun, List.foldl_append]

theorem onlineMVPCommittedTablesStep_row_eq [Fintype Outcome]
    [DecidableEq Row] [DecidableEq Outcome]
    (st : OnlineMVPCommittedTables Row Outcome) (r : Row) (x : Outcome) :
    onlineMVPCommittedRowView (onlineMVPCommittedTablesStep st r x) r =
      onlineMVPRowBatchStateStep (onlineMVPCommittedRowView st r) x := by
  by_cases hc : onlineMVPRowTrigger (st.base.total r + 1)
  · simp [onlineMVPCommittedRowView, onlineMVPCommittedTablesStep,
      onlineMVPCountTablesStep, onlineMVPRowBatchStateStep, hc,
      onlineMVP_pendingAfter_sum, Function.update_self]
  · simp [onlineMVPCommittedRowView, onlineMVPCommittedTablesStep,
      onlineMVPCountTablesStep, onlineMVPRowBatchStateStep, hc,
      Function.update_self]

theorem onlineMVPCommittedTablesStep_row_other [Fintype Outcome]
    [DecidableEq Row] [DecidableEq Outcome]
    (st : OnlineMVPCommittedTables Row Outcome) (r₀ r : Row) (x : Outcome)
    (h : r₀ ≠ r) :
    onlineMVPCommittedRowView (onlineMVPCommittedTablesStep st r₀ x) r =
      onlineMVPCommittedRowView st r := by
  by_cases hc : onlineMVPRowTrigger (st.base.total r₀ + 1)
  · simp [onlineMVPCommittedRowView, onlineMVPCommittedTablesStep,
      onlineMVPCountTablesStep, hc, h, Ne.symm h]
  · simp [onlineMVPCommittedRowView, onlineMVPCommittedTablesStep,
      onlineMVPCountTablesStep, hc, Ne.symm h]

/-- The retained per-row table is the row-local update applied to precisely
the chronological outcomes observed at that row. -/
theorem onlineMVPCommittedTablesRun_row_eq_visitList
    {Row Outcome : Type*} [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) (n : ℕ) (r : Row) :
    onlineMVPRowBatchStateRun (onlineMVPRowVisitList rowAt nextAt n r) =
      onlineMVPCommittedRowView (onlineMVPCommittedTablesRun rowAt nextAt n) r := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases hr : rowAt n = r
      · subst r
        simp [onlineMVPRowVisitList_succ]
        rw [onlineMVPRowBatchStateRun_append_one]
        change onlineMVPRowBatchStateStep
          (onlineMVPRowBatchStateRun (onlineMVPRowVisitList rowAt nextAt n (rowAt n)))
          (nextAt n) = _
        rw [onlineMVPCommittedTablesRun, onlineMVPCommittedTablesStep_row_eq]
        exact congrArg (fun s => onlineMVPRowBatchStateStep s (nextAt n)) ih
      · rw [onlineMVPRowVisitList_succ]
        simp only [if_neg hr, List.append_nil]
        rw [onlineMVPCommittedTablesRun, onlineMVPCommittedTablesStep_row_other _ _ _ _ hr]
        exact ih

end StatisticalRL.OnlineRL

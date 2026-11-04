import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Definitions of the MVP doubling-trigger row counters and realized-history fold. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- Power-of-two trigger, applied after incrementing the total row count. -/
def onlineMVPRowTrigger (n : ℕ) : Prop :=
  0 < n ∧ n = 2 ^ Nat.log2 n

instance onlineMVPRowTriggerDecidable (n : ℕ) : Decidable (onlineMVPRowTrigger n) := by
  unfold onlineMVPRowTrigger
  infer_instance

/-- State after n visits to one tagged row: (uncommitted batch, stored batch).
Only that row's accumulator is reset when its total reaches a trigger. -/
def onlineMVPRowCountState : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 =>
      let old := onlineMVPRowCountState n
      let nextBatch := old.1 + 1
      if onlineMVPRowTrigger (n + 1) then (0, nextBatch)
      else (nextBatch, old.2)

def onlineMVPStoredCount (n : ℕ) : ℕ := (onlineMVPRowCountState n).2

structure OnlineMVPCountTables (Row Outcome : Type*) where
  total : Row → ℕ
  pending : Row → Outcome → ℕ
  stored : Row → ℕ

def onlineMVPCountTablesInit (Row Outcome : Type*) : OnlineMVPCountTables Row Outcome :=
  ⟨fun _ => 0, fun _ _ => 0, fun _ => 0⟩

/-- One realized transition: first increment the total and the selected
successor counter. If the updated total is a power of two, store the sum of
that row's pending counters and reset only that row's pending counters. -/
def onlineMVPCountTablesStep {Row Outcome : Type*}
    [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (st : OnlineMVPCountTables Row Outcome) (r : Row) (x : Outcome) :
    OnlineMVPCountTables Row Outcome :=
  let nextTotal := st.total r + 1
  let pendingAfter := fun y => st.pending r y + if y = x then 1 else 0
  let commit := onlineMVPRowTrigger nextTotal
  { total := Function.update st.total r nextTotal
    pending := Function.update st.pending r (if commit then fun _ => 0 else pendingAfter)
    stored := if commit then Function.update st.stored r (∑ y : Outcome, pendingAfter y) else st.stored }

/-- Tables after the first n realized transitions. The input row and successor
sequences can be chosen adaptively; this deterministic fold assumes no
policy stationarity or probability law. -/
def onlineMVPCountTablesRun {Row Outcome : Type*}
    [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) : ℕ → OnlineMVPCountTables Row Outcome
  | 0 => onlineMVPCountTablesInit Row Outcome
  | n+1 => onlineMVPCountTablesStep (onlineMVPCountTablesRun rowAt nextAt n) (rowAt n) (nextAt n)


end StatisticalRL.OnlineRL

import Formalization.Online.Regret.MVP.MVPModelDefinitions
import Formalization.Online.Regret.MVP.MVPCountDefinitions
import Formalization.Online.Regret.MVP.OnlineMVPOperationalCounters
import Formalization.Online.Regret.MVP.MVPProfileDefinitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Private source-oriented development of committed successor histograms for the
power-of-two MVP update.  The scalar counter provider remains unchanged.  This
module enriches its state so a later source bridge can identify the empirical
kernel with the last completed dyadic batch.
-/

namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- The ordinary scalar table together with, for each row, the successor
histogram in the most recently committed batch.  The pending histogram is
already stored by `base.pending`. -/
structure OnlineMVPCommittedTables (Row Outcome : Type*) where
  base : OnlineMVPCountTables Row Outcome
  committed : Row → Outcome → ℕ

/-- Enriched initial table: both the scalar counters and committed histograms
start empty. -/
def onlineMVPCommittedTablesInit (Row Outcome : Type*) :
    OnlineMVPCommittedTables Row Outcome :=
  ⟨onlineMVPCountTablesInit Row Outcome, fun _ _ => 0⟩

/-- Erase only the extra histogram data. -/
def onlineMVPCommittedTablesErase {Row Outcome : Type*}
    (st : OnlineMVPCommittedTables Row Outcome) : OnlineMVPCountTables Row Outcome :=
  st.base

/-- One transition with retained committed successor histograms.  On a
row-local dyadic trigger it commits exactly the updated pending histogram and
the scalar state performs the original update; otherwise committed data is
unchanged. -/
def onlineMVPCommittedTablesStep {Row Outcome : Type*}
    [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (st : OnlineMVPCommittedTables Row Outcome) (r : Row) (x : Outcome) :
    OnlineMVPCommittedTables Row Outcome := by
  let nextTotal := st.base.total r + 1
  let pendingAfter := fun y : Outcome =>
    st.base.pending r y + if y = x then 1 else 0
  let commit := onlineMVPRowTrigger nextTotal
  exact
    { base := onlineMVPCountTablesStep st.base r x
      committed := if commit then Function.update st.committed r pendingAfter
                   else st.committed }

/-- Enriched state after the first `n` actual row/successor observations. -/
def onlineMVPCommittedTablesRun {Row Outcome : Type*}
    [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) : ℕ →
    OnlineMVPCommittedTables Row Outcome
  | 0 => onlineMVPCommittedTablesInit Row Outcome
  | n + 1 => onlineMVPCommittedTablesStep
      (onlineMVPCommittedTablesRun rowAt nextAt n) (rowAt n) (nextAt n)

theorem onlineMVPCommittedTablesErase_init (Row Outcome : Type*) :
    onlineMVPCommittedTablesErase (onlineMVPCommittedTablesInit Row Outcome) =
      onlineMVPCountTablesInit Row Outcome := rfl

theorem onlineMVPCommittedTablesErase_step {Row Outcome : Type*}
    [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (st : OnlineMVPCommittedTables Row Outcome) (r : Row) (x : Outcome) :
    onlineMVPCommittedTablesErase (onlineMVPCommittedTablesStep st r x) =
      onlineMVPCountTablesStep st.base r x := rfl

theorem onlineMVPCommittedTablesErase_run {Row Outcome : Type*}
    [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) (n : ℕ) :
    onlineMVPCommittedTablesErase (onlineMVPCommittedTablesRun rowAt nextAt n) =
      onlineMVPCountTablesRun rowAt nextAt n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hbase : (onlineMVPCommittedTablesRun rowAt nextAt n).base =
          onlineMVPCountTablesRun rowAt nextAt n := by
        simpa [onlineMVPCommittedTablesErase] using ih
      simpa [onlineMVPCountTablesRun] using
        congrArg (fun b => onlineMVPCountTablesStep b (rowAt n) (nextAt n)) hbase

/-- The committed histogram mass agrees with the scalar stored count, row by
row and after every finite realized history. -/
theorem onlineMVPCommittedTablesStep_mass_eq_stored {Row Outcome : Type*}
    [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (st : OnlineMVPCommittedTables Row Outcome) (r₀ : Row) (x : Outcome)
    (hmass : ∀ r, (∑ y : Outcome, st.committed r y) = st.base.stored r) :
    ∀ r, (∑ y : Outcome, (onlineMVPCommittedTablesStep st r₀ x).committed r y) =
      (onlineMVPCommittedTablesStep st r₀ x).base.stored r := by
  intro r
  by_cases hr : r₀ = r
  · subst r
    let pendingAfter := fun y : Outcome => st.base.pending r₀ y + if y = x then 1 else 0
    by_cases hc : onlineMVPRowTrigger (st.base.total r₀ + 1)
    · simp [onlineMVPCommittedTablesStep, onlineMVPCountTablesStep, pendingAfter, hc,
        Function.update_self, onlineMVP_pendingAfter_sum]
    · simp [onlineMVPCommittedTablesStep, onlineMVPCountTablesStep, pendingAfter, hc,
        Function.update_self, hmass r₀]
  · have hr' : r ≠ r₀ := Ne.symm hr
    by_cases hc : onlineMVPRowTrigger (st.base.total r₀ + 1)
    · simp [onlineMVPCommittedTablesStep, onlineMVPCountTablesStep, hc, hr',
        Function.update_of_ne, hmass r]
    · simp [onlineMVPCommittedTablesStep, onlineMVPCountTablesStep, hc, hmass r]

theorem onlineMVPCommittedTablesRun_mass_eq_stored {Row Outcome : Type*}
    [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) (n : ℕ) (r : Row) :
    (∑ x : Outcome, (onlineMVPCommittedTablesRun rowAt nextAt n).committed r x) =
      (onlineMVPCommittedTablesRun rowAt nextAt n).base.stored r := by
  induction n generalizing r with
  | zero => simp [onlineMVPCommittedTablesRun, onlineMVPCommittedTablesInit,
      onlineMVPCountTablesInit]
  | succ n ih =>
      have hall := onlineMVPCommittedTablesStep_mass_eq_stored
        (onlineMVPCommittedTablesRun rowAt nextAt n) (rowAt n) (nextAt n)
        (by intro r; exact ih r)
      exact hall r

end StatisticalRL.OnlineRL

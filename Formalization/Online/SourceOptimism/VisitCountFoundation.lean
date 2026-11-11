import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval

/-! Deterministic pre-episode visit/transition counts for online RL. No independent
visits, concentration, optimistic value or regret estimate is assumed. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- Before zero-indexed episode k, count the earlier episodes visiting row r
at a fixed source stage. For a finite-horizon application Row=State×Action. -/
noncomputable def onlineVisitCount {Row : Type*} (rowAt : ℕ → Row)
    (k : ℕ) (r : Row) : ℕ := by
  classical
  exact ((Finset.range k).filter (fun j => rowAt j = r)).card

theorem onlineVisitCount_zero {Row : Type*} (rowAt : ℕ → Row) (r : Row) :
    onlineVisitCount rowAt 0 r = 0 := by
  simp [onlineVisitCount]

/-- Each newly observed episode increments exactly the row it actually visits. -/
theorem onlineVisitCount_succ {Row : Type*} [DecidableEq Row] (rowAt : ℕ → Row) (k : ℕ) (r : Row) :
    onlineVisitCount rowAt (k + 1) r =
      onlineVisitCount rowAt k r + (if rowAt k = r then 1 else 0) := by
  classical
  by_cases hr : rowAt k = r
  · simp [onlineVisitCount, Finset.range_add_one, hr, Finset.filter_insert, Finset.mem_filter,
      Nat.add_comm]
  · simp [onlineVisitCount, Finset.range_add_one, Finset.filter_insert, hr]

end StatisticalRL.OnlineRL

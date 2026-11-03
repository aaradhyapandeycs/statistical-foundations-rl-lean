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

/-- Actual successor counts within the same earlier-episode visit set. -/
noncomputable def onlineTransitionCount {Row State : Type*}
    (rowAt : ℕ → Row) (nextAt : ℕ → State) (k : ℕ) (r : Row) (x : State) : ℕ := by
  classical
  exact (((Finset.range k).filter (fun j => rowAt j = r)).filter
    (fun j => nextAt j = x)).card

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

/-- Counts conserve mass before any empirical division. In particular, a
positive denominator produces a normalized empirical successor distribution. -/
theorem onlineTransitionCount_sum {Row State : Type*} [Fintype State]
    (rowAt : ℕ → Row) (nextAt : ℕ → State) (k : ℕ) (r : Row) :
    ∑ x, onlineTransitionCount rowAt nextAt k r x = onlineVisitCount rowAt k r := by
  classical
  unfold onlineTransitionCount onlineVisitCount
  simpa using (Finset.card_eq_sum_card_fiberwise
    (s := (Finset.range k).filter (fun j => rowAt j = r))
    (t := Finset.univ) (f := nextAt) (fun _ _ => Finset.mem_univ _)).symm

/-- Strict past dependence: the current and later episodes do not affect the
pre-episode count. This deterministic fact does not assume iid visitation. -/
theorem onlineVisitCount_prefix_congr {Row : Type*}
    (rowAt rowAt' : ℕ → Row) (k : ℕ)
    (h : ∀ j, j < k → rowAt j = rowAt' j) (r : Row) :
    onlineVisitCount rowAt k r = onlineVisitCount rowAt' k r := by
  classical
  unfold onlineVisitCount
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

end StatisticalRL.OnlineRL

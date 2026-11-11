import Formalization.Online.SourceOptimism.RowOutcomeDefinitions
import Mathlib.Data.List.Range
import Mathlib.Data.List.Basic

/-! Adaptive deterministic stack consumption;
no online sampling-law coupling or concentration theorem is assumed/proved. -/
namespace StatisticalRL.OnlineRL
variable {Row Outcome : Type*} [DecidableEq Row]

/-- Choose the next row using only the revealed history, then read exactly
its next unused successor. Total streams are deterministic inputs here. -/
def onlineStackHistory
    (choose : List (Row × Outcome) → Row) (stream : Row → ℕ → Outcome) :
    ℕ → List (Row × Outcome)
  | 0 => []
  | n+1 =>
    let history := onlineStackHistory choose stream n
    let r := choose history
    history ++ [(r, stream r (onlineRowOutcomes history r).length)]

/-- Appending one revealed transition updates only its selected row. -/
theorem onlineRowOutcomes_append_one
    (history : List (Row × Outcome)) (r q : Row) (x : Outcome) :
    onlineRowOutcomes (history++[(q,x)]) r =
      onlineRowOutcomes history r ++ (if q=r then [x] else []) := by
  by_cases h : q = r
  · simp [onlineRowOutcomes, List.filterMap_append, h]
  · simp [onlineRowOutcomes, List.filterMap_append, h]

/-- One transition is revealed at each chronological step. -/
theorem onlineStackHistory_length
    (choose : List (Row × Outcome) → Row) (stream : Row → ℕ → Outcome) (n : ℕ) :
    (onlineStackHistory choose stream n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [onlineStackHistory, ih]

/-- The row outcomes are exactly an initial stream prefix even though the
choices of row may depend arbitrarily on previously revealed outcomes. -/
theorem onlineStackHistory_row_prefix
    (choose : List (Row × Outcome) → Row) (stream : Row → ℕ → Outcome) :
    ∀ n r, onlineRowOutcomes (onlineStackHistory choose stream n) r =
      (List.range (onlineRowOutcomes (onlineStackHistory choose stream n) r).length).map
        (stream r) := by
  intro n
  induction n with
  | zero => intro r; rfl
  | succ n ih =>
    intro r
    let history := onlineStackHistory choose stream n
    let q := choose history
    have hp := ih r
    change onlineRowOutcomes
      (history++[(q,stream q (onlineRowOutcomes history q).length)]) r =
      (List.range (onlineRowOutcomes
        (history++[(q,stream q (onlineRowOutcomes history q).length)]) r).length).map (stream r)
    simp only [onlineRowOutcomes_append_one]
    by_cases hq : q=r
    · simp only [hq, ite_true, List.length_append, List.length_singleton]
      rw [List.range_succ, List.map_append]
      change onlineRowOutcomes history r ++ [stream r (onlineRowOutcomes history r).length] =
        (List.range (onlineRowOutcomes history r).length).map (stream r) ++
          [stream r (onlineRowOutcomes history r).length]
      exact congrArg (fun xs => xs++[stream r (onlineRowOutcomes history r).length]) hp
    · simp only [if_neg hq, List.append_nil]
      exact hp

end StatisticalRL.OnlineRL

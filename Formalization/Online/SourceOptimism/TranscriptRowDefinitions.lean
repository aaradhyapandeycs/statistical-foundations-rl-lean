import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic

namespace StatisticalRL.OnlineRL
variable {Row Outcome : Type*} [Fintype Row] [Fintype Outcome] [DecidableEq Row]

/-- Every finite transcript has a total row enumeration, without an assumption
about unrevealed future rows or a change to its observed rows. -/
def onlineTranscriptRowSequence (fallback : Row) (history : List (Row × Outcome)) (j : ℕ) : Row :=
  if hj : j<history.length then (history.get ⟨j,hj⟩).1 else fallback


end StatisticalRL.OnlineRL

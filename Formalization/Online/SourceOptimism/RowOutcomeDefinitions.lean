import Mathlib.Data.List.Basic
namespace StatisticalRL.OnlineRL
variable {Row Outcome : Type*} [DecidableEq Row]
/-- Chronological outcomes previously revealed from one row. -/
def onlineRowOutcomes (history : List (Row × Outcome)) (r : Row) : List Outcome :=
  history.filterMap (fun pair => if pair.1=r then some pair.2 else none)


end StatisticalRL.OnlineRL

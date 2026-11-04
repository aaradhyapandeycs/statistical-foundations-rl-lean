import Formalization.Online.Regret.MVP.Model.OnlineMVPRowBatchIdentity
import Formalization.Online.SourceOptimism.SuccessorStackPrefix

/-! MVP's operational row/outcome arrays agree with the actual stack transcript. -/
namespace StatisticalRL.OnlineRL
variable {Row Outcome : Type*} [DecidableEq Row] [DecidableEq Outcome]

def mvpStackRowAt (choose : List (Row × Outcome) → Row) (stream : Row → ℕ → Outcome)
    (n : ℕ) : Row := choose (onlineStackHistory choose stream n)

def mvpStackNextAt (choose : List (Row × Outcome) → Row) (stream : Row → ℕ → Outcome)
    (n : ℕ) : Outcome :=
  let history := onlineStackHistory choose stream n
  let r := choose history
  stream r (onlineRowOutcomes history r).length

/-- The chronological filtered array of the operational MVP fold is exactly
the actual stack's observed outcomes, for any causal row chooser. -/
theorem mvpStackRowVisitList_eq_observed (choose : List (Row × Outcome) → Row)
    (stream : Row → ℕ → Outcome) (n : ℕ) (r : Row) :
    onlineMVPRowVisitList (mvpStackRowAt choose stream) (mvpStackNextAt choose stream) n r =
      onlineRowOutcomes (onlineStackHistory choose stream n) r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [onlineMVPRowVisitList_succ, onlineStackHistory, onlineRowOutcomes_append_one, ← ih]
    rfl
end StatisticalRL.OnlineRL

import Formalization.Online.Regret.MVP.Optimism.MVPActualStackRowVisit
import Formalization.Online.Regret.MVP.Optimism.MVPBatchSliceList
import Formalization.Online.Regret.MVP.Model.OnlineMVPRowDyadicBatch
import Formalization.Online.SourceOptimism.ObservedEmpiricalPrefix

/-! Source-only draft: the retained batch is a deterministic slice of the
actual chronological row observations.  No random-count independence is used. -/
namespace StatisticalRL.OnlineRL

theorem mvp_sourceBatch_dyadic_fit {Outcome : Type*} [DecidableEq Outcome]
    (xs : List Outcome) (h : 2 ≤ xs.length) :
    2 * onlineMVPStoredCount xs.length ≤ xs.length := by
  simpa [onlineMVPSourceBatchEnd, show ¬ xs.length < 2 by omega] using
    onlineMVPSourceBatchEnd_le xs.length

/-- Each element of a retained batch agrees with the corresponding offset in
the actual row stream, even when the row is chosen adaptively. -/
theorem mvp_sourceBatch_get_stack {Row Outcome : Type*}
    [Fintype Row] [DecidableEq Row] [Fintype Outcome] [DecidableEq Outcome]
    (choose : List (Row × Outcome) → Row) (stream : Row → ℕ → Outcome)
    (t : ℕ) (r : Row)
    (h : 2 ≤ (onlineRowOutcomes (onlineStackHistory choose stream t) r).length)
    (j : Fin (onlineMVPStoredCount
      (onlineRowOutcomes (onlineStackHistory choose stream t) r).length)) :
    (onlineMVPSourceBatchList
      (onlineRowOutcomes (onlineStackHistory choose stream t) r)).get
        ⟨j.val, by rw [onlineMVPSourceBatchList_length]; exact j.isLt⟩ =
      stream r (onlineMVPStoredCount
        (onlineRowOutcomes (onlineStackHistory choose stream t) r).length + j.val) := by
  let xs := onlineRowOutcomes (onlineStackHistory choose stream t) r
  have hfit : 2 * onlineMVPStoredCount xs.length ≤ xs.length :=
    mvp_sourceBatch_dyadic_fit xs h
  have hg := mvp_takeDropBatch_get xs (onlineMVPStoredCount xs.length) hfit j
  dsimp [xs] at hfit
  have ho := onlineStackHistory_observedRowData choose stream t r
    ⟨onlineMVPStoredCount (onlineRowOutcomes (onlineStackHistory choose stream t) r).length + j.val, by have := j.isLt; omega⟩
  simpa [xs, onlineObservedRowData, onlineMVPSourceBatchList,
    onlineMVPSourceBatchStart, onlineMVPSourceBatchEnd, show ¬ (onlineRowOutcomes (onlineStackHistory choose stream t) r).length < 2 by omega] using hg.trans ho

end StatisticalRL.OnlineRL

import Formalization.Online.Regret.MVP.Optimism.MVPCommittedBatchSlice
import Formalization.Online.Regret.MVP.Optimism.MVPBatchFuture

/-! The retained positive-size batch agrees pointwise with its deterministic
finite-stack slice on the same realized adaptive history. -/
namespace StatisticalRL.OnlineRL

theorem mvp_retainedBatch_eq_finiteStackSlice {Row Outcome : Type*}
    [Fintype Row] [DecidableEq Row] [Fintype Outcome] [DecidableEq Outcome]
    (choose : List (Row × Outcome) → Row) (K : ℕ) (fallback : Outcome)
    (data : Row × Fin K → Outcome) (t : ℕ) (r : Row)
    (h : 2 ≤ (onlineRowOutcomes (onlineStackHistory choose
      (onlineFiniteStackExtend K fallback data) t) r).length)
    (hcount : (onlineRowOutcomes (onlineStackHistory choose
      (onlineFiniteStackExtend K fallback data) t) r).length ≤ K) :
    let xs := onlineRowOutcomes (onlineStackHistory choose
      (onlineFiniteStackExtend K fallback data) t) r
    let m := onlineMVPStoredCount xs.length
    ∀ j : Fin m,
      (onlineMVPSourceBatchList xs).get
        ⟨j.val, by rw [onlineMVPSourceBatchList_length]; exact j.isLt⟩ =
      data (r, mvpBatchIndex K m (by exact (mvp_sourceBatch_dyadic_fit xs h).trans hcount) j) := by
  dsimp only
  intro j
  have hg := mvp_sourceBatch_get_stack choose (onlineFiniteStackExtend K fallback data) t r h j
  have hfit := mvp_sourceBatch_dyadic_fit
    (onlineRowOutcomes (onlineStackHistory choose (onlineFiniteStackExtend K fallback data) t) r) h
  have hj := j.isLt
  have hlt : onlineMVPStoredCount (onlineRowOutcomes (onlineStackHistory choose
      (onlineFiniteStackExtend K fallback data) t) r).length + j.val < K := by omega
  simpa [onlineFiniteStackExtend, mvpBatchIndex, hlt] using hg

end StatisticalRL.OnlineRL

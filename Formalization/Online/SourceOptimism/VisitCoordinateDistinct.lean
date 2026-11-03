import Formalization.Online.SourceOptimism.VisitCountFoundation

/-! Distinct fixed history labels for the
successor-stack product cylinder; no probabilistic premise is supplied. -/
namespace StatisticalRL.OnlineRL
variable {Row : Type*} [DecidableEq Row]

/-- Counts increase with the revealed prefix, pathwise. -/
theorem onlineVisitCount_mono_prefix (rowAt : ℕ → Row) (j k : ℕ) (hjk : j≤k) (r : Row) :
    onlineVisitCount rowAt j r ≤ onlineVisitCount rowAt k r := by
  classical
  unfold onlineVisitCount
  apply Finset.card_le_card
  intro n hn
  have hn' : n < j ∧ rowAt n = r := by
    simpa only [Finset.mem_filter, Finset.mem_range] using hn
  simpa only [Finset.mem_filter, Finset.mem_range] using
    (show n < k ∧ rowAt n = r from ⟨hn'.1.trans_le hjk, hn'.2⟩)

/-- Two different chronological visits to the same row use strictly increasing
stream indices, irrespective of how the row choices depended on outcomes. -/
theorem onlineVisitCoordinate_index_strict
    (rowAt : ℕ → Row) (j k : ℕ) (hjk : j<k) (hrow : rowAt j=rowAt k) :
    onlineVisitCount rowAt j (rowAt j) < onlineVisitCount rowAt k (rowAt k) := by
  have hm := onlineVisitCount_mono_prefix rowAt (j+1) k (by omega) (rowAt j)
  rw [onlineVisitCount_succ] at hm
  simp only [ite_true] at hm
  rw [← hrow]
  omega

/-- All (row, pre-visit count) labels of a finite realized history are distinct.
This is the missing deterministic freshness input to cylinder factorization. -/
theorem onlineVisitCoordinate_injective
    (rowAt : ℕ → Row) (n : ℕ) :
    Function.Injective (fun j : Fin n =>
      (rowAt j.val,onlineVisitCount rowAt j.val (rowAt j.val))) := by
  intro j k heq
  have hrow := congrArg Prod.fst heq
  have hcount := congrArg Prod.snd heq
  change rowAt j.val = rowAt k.val at hrow
  change onlineVisitCount rowAt j.val (rowAt j.val) =
    onlineVisitCount rowAt k.val (rowAt k.val) at hcount
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · have hs := onlineVisitCoordinate_index_strict rowAt j.val k.val hlt hrow
    exact (ne_of_lt hs) hcount
  · have hs := onlineVisitCoordinate_index_strict rowAt k.val j.val hgt hrow.symm
    exact (ne_of_lt hs) hcount.symm

end StatisticalRL.OnlineRL

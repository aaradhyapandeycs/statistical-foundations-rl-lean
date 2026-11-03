import Formalization.Online.SourceOptimism.VisitCoordinateDistinct
import Mathlib.Data.Nat.Basic

/-! Chronological KH steps require only K
slots for each stage-tagged row. No actual-law premise is supplied. -/
namespace StatisticalRL.OnlineRL
variable {Row : Type*} [DecidableEq Row] {H : ℕ}

/-- A chronological visit history whose tags cycle through source stages has
at most floor(n/H) prior visits to its current stage-tagged row. -/
theorem onlineChronologicalStageCount_le_episode
    (rowAt : ℕ → Fin H × Row) (n : ℕ) (r : Fin H × Row)
    (hstage : ∀ j, j<n → (rowAt j).1.val=j%H)
    (hrstage : r.1.val=n%H) :
    onlineVisitCount rowAt n r ≤ n/H := by
  classical
  letI : DecidableEq (Fin H × Row) := Classical.decEq _
  let S := (Finset.range n).filter (fun j => rowAt j=r)
  have hmods (j : ℕ) (hj : j∈S) : j%H=n%H := by
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have heq := congrArg (fun q : Fin H × Row => q.1.val) (Finset.mem_filter.mp hj).2
    exact (hstage j hlt).symm.trans (heq.trans hrstage)
  have hm : Set.MapsTo (fun j : ℕ => j/H) S (Finset.range (n/H)) := by
    intro j hj
    have hjn := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    apply Finset.mem_range.mpr
    change j/H < n/H
    have hle : j/H≤n/H := Nat.div_le_div_right hjn.le
    by_contra hnot
    have hquot : j/H=n/H := by omega
    have heq : j=n := by
      calc
        j = j%H+H*(j/H) := (Nat.mod_add_div j H).symm
        _ = n%H+H*(n/H) := by rw [hmods j hj,hquot]
        _ = n := Nat.mod_add_div n H
    omega
  have hinj : Set.InjOn (fun j : ℕ => j/H) S := by
    intro j hj k hk hquot
    change j/H = k/H at hquot
    calc
      j = j%H+H*(j/H) := (Nat.mod_add_div j H).symm
      _ = k%H+H*(k/H) := by rw [hmods j hj,hmods k hk,hquot]
      _ = k := Nat.mod_add_div k H
  have hc := Finset.card_le_card_of_injOn (fun j : ℕ => j/H) hm hinj
  simpa [S,onlineVisitCount] using hc

/-- The next successor draw in a KH-step experiment is in its row's K-slot
stack, even though the total chronological horizon may be much larger than K. -/
theorem onlineChronologicalStageCount_lt_K
    (rowAt : ℕ → Fin H × Row) (K n : ℕ) (hH : 0<H) (hn : n<K*H)
    (r : Fin H × Row)
    (hstage : ∀ j, j<n → (rowAt j).1.val=j%H)
    (hrstage : r.1.val=n%H) :
    onlineVisitCount rowAt n r < K := by
  have hc := onlineChronologicalStageCount_le_episode rowAt n r hstage hrstage
  have hq : n/H<K := (Nat.div_lt_iff_lt_mul hH).2 (by simpa [Nat.mul_comm] using hn)
  exact hc.trans_lt hq

end StatisticalRL.OnlineRL

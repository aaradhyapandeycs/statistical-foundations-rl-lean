import Formalization.Online.SourceOptimism.ChronologicalStageStackCap

/-! Any stage-tagged row has at most k
samples after k completed episodes, including stages other than the next stage. -/
namespace StatisticalRL.OnlineRL
variable {Row : Type*} [DecidableEq Row] {H : ℕ}

/-- The pre-episode empirical model uses a bounded prefix for every row, not
only for the stage-zero row that will be queried next. -/
theorem onlineVisitCount_completedEpisodes_le
    (rowAt : ℕ → Fin H × Row) (k : ℕ) (hH : 0<H) (r : Fin H × Row)
    (hstage : ∀ j,j<k*H → (rowAt j).1.val=j%H) :
    onlineVisitCount rowAt (k*H) r≤k := by
  classical
  letI : DecidableEq (Fin H × Row) := Classical.decEq _
  let S := (Finset.range (k*H)).filter (fun j => rowAt j=r)
  have hmod (j : ℕ) (hj : j∈S) : j%H=r.1.val := by
    have hjlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hr := congrArg (fun q : Fin H × Row => q.1.val) (Finset.mem_filter.mp hj).2
    exact (hstage j hjlt).symm.trans hr
  have hm : Set.MapsTo (fun j : ℕ => j/H) S (Finset.range k) := by
    intro j hj
    apply Finset.mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hH).2
      (by simpa [Nat.mul_comm] using Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  have hi : Set.InjOn (fun j : ℕ => j/H) S := by
    intro j hj ℓ hℓ hq
    change j/H = ℓ/H at hq
    calc
      j=j%H+H*(j/H) := (Nat.mod_add_div j H).symm
      _=ℓ%H+H*(ℓ/H) := by rw [hmod j hj,hmod ℓ hℓ,hq]
      _=ℓ := Nat.mod_add_div ℓ H
  have hc := Finset.card_le_card_of_injOn (fun j : ℕ => j/H) hm hi
  simpa [S,onlineVisitCount] using hc

end StatisticalRL.OnlineRL

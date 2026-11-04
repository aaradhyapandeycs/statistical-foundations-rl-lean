import Formalization.Online.SourceOptimism.CompletedEpisodeCount
import Formalization.Online.SourceOptimism.StackRunCylinderIdentity

/-! OnlineW1StageEpisodeCount: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
variable {Row : Type*} [DecidableEq Row] {H : ℕ}

/-- In a stage-tagged history, the number of occurrences of a row before
k completed episodes is exactly the number of earlier episodes whose stage-h
row is that row. -/
theorem onlineVisitCount_stage_episode_eq
    (rowAt : ℕ → Fin H × Row) (h : Fin H) (k : ℕ) (hH : 0 < H)
    (r : Fin H × Row) (hr : r.1 = h)
    (hstage : ∀ j, j < k * H → (rowAt j).1.val = j % H) :
    onlineVisitCount rowAt (k * H) r =
      onlineVisitCount (fun e => rowAt (e * H + h.val)) k r := by
  classical
  let A := (Finset.range (k * H)).filter (fun j => rowAt j = r)
  let B := (Finset.range k).filter (fun e => rowAt (e * H + h.val) = r)
  have hmod (j : ℕ) (hj : j ∈ A) : j % H = h.val := by
    have hm := Finset.mem_filter.mp hj
    have ht := hstage j (Finset.mem_range.mp hm.1)
    have he := congrArg (fun x : Fin H × Row => x.1.val) hm.2
    simpa [hr] using ht.symm.trans he
  have hrep (j : ℕ) (hj : j ∈ A) : j / H * H + h.val = j := by
    have hd := Nat.mod_add_div j H
    rw [hmod j hj] at hd
    simpa [Nat.mul_comm, Nat.add_comm] using hd
  have hcard : A.card = B.card := by
   apply Finset.card_bij' (fun j _ => j / H) (fun e _ => e * H + h.val)
   · intro j hj
     have hm := Finset.mem_filter.mp hj
     apply Finset.mem_filter.mpr
     constructor
     · apply Finset.mem_range.mpr
       exact (Nat.div_lt_iff_lt_mul hH).2 (by simpa [Nat.mul_comm] using Finset.mem_range.mp hm.1)
     · rw [hrep j hj]
       exact hm.2
   · intro e he
     have hm := Finset.mem_filter.mp he
     apply Finset.mem_filter.mpr
     constructor
     · apply Finset.mem_range.mpr
       have heK := Finset.mem_range.mp hm.1
       calc
         e * H + h.val < e * H + H := Nat.add_lt_add_left h.isLt _
         _ = (e + 1) * H := by rw [Nat.succ_mul]
         _ ≤ k * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt heK)
     · exact hm.2
   · intro j hj
     exact hrep j hj
   · intro e he
     rw [Nat.add_comm, Nat.mul_comm e H, Nat.add_mul_div_left _ _ hH]
     simp [Nat.div_eq_of_lt h.isLt]
  unfold onlineVisitCount
  simp only [A, B] at hcard
  convert hcard using 2 <;> ext x <;> simp

/-- The same correspondence applies directly to a completed-history observed
row count, via the existing transcript enumeration identity. -/
theorem onlineObserved_stage_episode_count_eq
    {Outcome : Type*} (history : List ((Fin H × Row) × Outcome))
    (rowAt : ℕ → Fin H × Row) (h : Fin H) (k : ℕ) (hH : 0 < H)
    (hk : k * H ≤ history.length) (r : Fin H × Row) (hr : r.1 = h)
    (hrows : ∀ j : Fin history.length, rowAt j.val = (history.get j).1)
    (hstage : ∀ j, j < k * H → (rowAt j).1.val = j % H) :
    (onlineRowOutcomes (history.take (k * H)) r).length =
      onlineVisitCount (fun e => rowAt (e * H + h.val)) k r := by
  rw [onlineTranscript_rowCount_eq_visitCount history rowAt hrows (k * H) hk r]
  exact onlineVisitCount_stage_episode_eq rowAt h k hH r hr hstage
end StatisticalRL.OnlineRL

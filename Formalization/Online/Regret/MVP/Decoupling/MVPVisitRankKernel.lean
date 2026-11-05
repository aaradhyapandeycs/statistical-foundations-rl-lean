import Formalization.Online.Regret.MVP.Decoupling.MVPDyadicSlotSums
import Formalization.Probability.Variance

/-! rank-indexed row representation. Its finite rank domain excludes
out-of-range rows; only the scalar error is extended by zero elsewhere. -/
namespace StatisticalRL.OnlineRL

/-- For a noninitial rank u<K, the source batch level is log₂u−1. -/
def mvp_rankBatchLevel (K u : ℕ) (hu : u<K) (h2 : 2≤u) : Fin (Nat.log2 K) := by
  have hm : Nat.log2 u ≤ Nat.log2 K := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right hu.le
  have hlo : 1 ≤ Nat.log2 u := (Nat.le_log2 (by omega)).2 (by simpa using h2)
  exact ⟨Nat.log2 u-1,by omega⟩

theorem mvp_rankBatchLevel_at_slot (K : ℕ) (j : Fin (Nat.log2 K))
    (i : ℕ) (hi : i<2*2^j.val) (hu : 2*2^j.val+i<K) :
    mvp_rankBatchLevel K (2*2^j.val+i) hu (by
      have hp : 0 < 2^j.val := by positivity
      omega) = j := by
  apply Fin.ext
  change Nat.log2 (2*2^j.val+i)-1 = j.val
  rw [mvp_dyadicSlot_log2 _ _ hi]
  omega

noncomputable def mvp_visitRankKernel {State : Type*} [Fintype State]
    (K : ℕ) (initial first : FiniteDistribution State)
    (batch : Fin (Nat.log2 K) → FiniteDistribution State) (u : Fin K) : FiniteDistribution State :=
  if hzero : u.val=0 then initial else
  if hone : u.val=1 then first else batch (mvp_rankBatchLevel K u.val u.isLt (by omega))

theorem mvp_visitRankKernel_at_slot {State : Type*} [Fintype State]
    (K : ℕ) (initial first : FiniteDistribution State)
    (batch : Fin (Nat.log2 K) → FiniteDistribution State)
    (j : Fin (Nat.log2 K)) (i : ℕ) (hi : i<2*2^j.val) (hu : 2*2^j.val+i<K) :
    mvp_visitRankKernel K initial first batch ⟨2*2^j.val+i,hu⟩ = batch j := by
  have hp : 0 < 2^j.val := by positivity
  have hn0 : 2*2^j.val+i≠0 := by omega
  have hn1 : 2*2^j.val+i≠1 := by omega
  simp only [mvp_visitRankKernel,dif_neg hn0,dif_neg hn1]
  rw [mvp_rankBatchLevel_at_slot K j i hi hu]

variable {State : Type*} [Fintype State]
noncomputable def mvp_rowPositiveError (p q : FiniteDistribution State) (V : State → ℝ) : ℝ :=
  max (q.expectation V-p.expectation V) 0

theorem mvp_rowPositiveError_zero (p q : FiniteDistribution State) :
    mvp_rowPositiveError p q 0 = 0 := by
  unfold mvp_rowPositiveError
  change max (q.expectation (fun _=>0)-p.expectation (fun _=>0)) 0=0
  rw [p.expectation_const,q.expectation_const]
  norm_num

theorem mvp_rowPositiveError_le (p q : FiniteDistribution State)
    (V : State → ℝ) (H : ℝ) (hH : 0≤H) (hV : ∀ s,0≤V s∧V s≤H) :
    mvp_rowPositiveError p q V ≤ H := by
  apply max_le
  · have hp := p.expectation_nonneg (fun s=>(hV s).1)
    have hq := q.expectation_le_const (fun s=>(hV s).2)
    linarith only [hp,hq]
  · exact hH

end StatisticalRL.OnlineRL

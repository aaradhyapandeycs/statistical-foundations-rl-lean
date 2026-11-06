import Formalization.Online.QLearning.PropagationBudget
import Formalization.Online.QLearning.VisitRank
import Mathlib.Data.List.NodupEquivFin

/-! Exact ordered-visit list to chronological matrix identity. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row : Type*} [Fintype Row]
attribute [local instance] Classical.propDecidable

theorem qLearning_visitList_to_matrix (H K k : ℕ) (hk : k<K)
    (rowAt : ℕ → Row) (gap : ℕ → ℝ) :
    let visits := (List.range k).filter (fun e => rowAt e = rowAt k)
    let t := visits.length
    (∑ i : Fin t, onlineQRateWeight H t (i.val+1)*gap (visits.get i)) =
      ∑ e ∈ (Finset.range K).filter (fun e => e<k ∧ rowAt k=rowAt e),
        onlineQRateWeight H (onlineVisitCount rowAt k (rowAt k))
          (onlineVisitCount rowAt e (rowAt e)+1)*gap e := by
  classical
  let visits := (List.range k).filter (fun e => rowAt e = rowAt k)
  let t := visits.length
  let s := (Finset.range K).filter (fun e => e<k ∧ rowAt k=rowAt e)
  have hlen : t = onlineVisitCount rowAt k (rowAt k) :=
    by simpa only [t,visits] using qLearningRangeVisits_length rowAt k (rowAt k)
  have hnodup : visits.Nodup := (List.nodup_range).filter _
  change (∑ i : Fin t, onlineQRateWeight H t (i.val+1)*gap (visits.get i)) =
    ∑ e ∈ s, onlineQRateWeight H (onlineVisitCount rowAt k (rowAt k))
      (onlineVisitCount rowAt e (rowAt e)+1)*gap e
  apply Finset.sum_bij (fun i _ => visits.get i)
  · intro i hi
    have hm : visits.get i ∈ visits := List.get_mem _ _
    have hm' : visits.get i < k ∧ rowAt (visits.get i)=rowAt k := by simpa only [visits,List.mem_filter,List.mem_range,decide_eq_true_eq] using hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hm'.1.trans hk),hm'.1,hm'.2.symm⟩
  · intro i hi j hj he
    exact hnodup.get_inj_iff.mp he
  · intro e he
    have hm := (Finset.mem_filter.mp he).2
    have hmem : e ∈ visits := by simp [visits,hm.1,hm.2.symm]
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hmem
    exact ⟨i,Finset.mem_univ _,hi⟩
  · intro i hi
    have hm : visits.get i ∈ visits := List.get_mem _ _
    have hm' : visits.get i < k ∧ rowAt (visits.get i)=rowAt k := by
      simpa only [visits,List.mem_filter,List.mem_range,decide_eq_true_eq] using hm
    have hrow : rowAt (visits.get i)=rowAt k := hm'.2
    have hrank := qLearningFilteredRange_get_rank (fun e => rowAt e = rowAt k) k i
    have hrank' : onlineVisitCount rowAt (visits.get i) (rowAt k) = i.val := by
      rw [← qLearningRangeVisits_length]
      simpa only [visits] using hrank
    simp only [hrow,hrank',hlen]
end StatisticalRL.OnlineRL

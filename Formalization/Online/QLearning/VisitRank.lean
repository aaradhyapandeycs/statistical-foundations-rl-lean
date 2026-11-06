import Formalization.Online.QLearning.ActualWeightedEpisode
import Mathlib.Data.List.GetD

/-! rank identity. Counts and indices are computed
from actual histories; no rank or concentration certificate is assumed. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- For an ordered filtered natural range, the number of earlier selected
indices equals the zero-based position of any selected entry. -/
theorem qLearningFilteredRange_get_rank (p : ℕ → Prop) [DecidablePred p] (n : ℕ)
    (i : Fin ((List.range n).filter p).length) :
    (((List.range (((List.range n).filter p).get i)).filter p).length) = i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      by_cases hn : p n
      · have hlist : (List.range (n+1)).filter p = (List.range n).filter p ++ [n] := by
          simp [List.range_succ, hn]
        have hi : i.val < ((List.range n).filter p).length + 1 := by simpa [hlist] using i.isLt
        by_cases hold : i.val < ((List.range n).filter p).length
        · let j : Fin ((List.range n).filter p).length := ⟨i.val,hold⟩
          have he : ((List.range (n+1)).filter p).get i = ((List.range n).filter p).get j := by
            simp [List.get_eq_getElem, hlist, List.getElem_append_left, hold, j]
          rw [he]
          exact ih j
        · have heq : i.val = ((List.range n).filter p).length := by omega
          have he : ((List.range (n+1)).filter p).get i = n := by
            simp [List.get_eq_getElem, hlist, List.getElem_append_right, heq]
          rw [he,heq]
      · have hlist : (List.range (n+1)).filter p = (List.range n).filter p := by
          simp [List.range_succ, hn]
        let j : Fin ((List.range n).filter p).length := ⟨i.val, by simpa [hlist] using i.isLt⟩
        have he : ((List.range (n+1)).filter p).get i = ((List.range n).filter p).get j := by
          simp [List.get_eq_getElem, hlist, j]
        rw [he]
        exact ih j

/-- The actual pre-episode count at the i-th earlier visit equals i (zero-based).
The i+1-st update therefore uses `onlineQRate H (i+1)` and `bonus (i+1)`. -/
theorem qLearningActualVisitEpisode_rank {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H)
    (i : Fin (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length) :
    let e := (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).get i
    let he : e < K := lt_trans ((qLearningActualVisitEpisode_get_mem hH E bonus initial fallback path k r i).1) k.isLt
    (qLearningActualTableAt hH E bonus initial fallback path (e*H)).count r = i.val := by
  classical
  let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
  let e := visits.get i
  have heK : e < K := lt_trans ((qLearningActualVisitEpisode_get_mem hH E bonus initial fallback path k r i).1) k.isLt
  have hlen := qLearningActualVisitEpisodes_length hH E bonus initial fallback path ⟨e,heK⟩ r
  have hrank := qLearningFilteredRange_get_rank
    (fun t => onlineTranscriptRowSequence
      ((onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)) [])
      (qLearningActualSequentialHistory hH E bonus initial fallback path) (t*H+r.1.val) = r) k.val i
  change (qLearningActualTableAt hH E bonus initial fallback path (e*H)).count r = i.val
  rw [← hlen.1]
  simpa [visits, e, qLearningActualVisitEpisodes] using hrank

end StatisticalRL.OnlineRL

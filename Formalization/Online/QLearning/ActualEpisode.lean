import Formalization.Online.QLearning.ActualConsumer
import Formalization.Online.QLearning.ActualEpisodeDefinitions
import Formalization.Online.SourceOptimism.SequentialTranscriptUniqueness
import Formalization.Online.SourceOptimism.SequentialEpisodeLaw

/-! actual sequential-episode bridge. The source optimism
and concentration conclusions are not assumed or proved here. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- Source weighted representation specialized to the actual sequential history.
The index log consists of actual pre-update table targets, including true observed
successors; identification with episode-indexed visits is a further bridge. -/
theorem qLearningActualTableAt_weighted {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (n : ℕ) (r : OnlineMDPRow State Action H) :
    let hist := (qLearningActualSequentialHistory hH E bonus initial fallback path).take n
    let log := (qLearningLoggedVisitFold hH E bonus r (qLearningChronologicalInitial H) hist).2
    (qLearningActualTableAt hH E bonus initial fallback path n).q r =
      onlineQRateWeight H log.length 0 * H +
        ∑ i ∈ Finset.Icc 1 log.length, onlineQRateWeight H log.length i * log.getD (i-1) 0 := by
  simpa [qLearningActualTableAt, qLearningChronologicalInitial] using
    qLearningActualFold_weighted hH E bonus r (qLearningChronologicalInitial H) rfl
      ((qLearningActualSequentialHistory hH E bonus initial fallback path).take n)

/-- Every row in the reconstructed transcript has its actual chronological
stage label, including the terminal stage of each episode. -/
theorem qLearningActualSequentialHistory_stage {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (j : Fin (qLearningActualSequentialHistory hH E bonus initial fallback path).length) :
    ((qLearningActualSequentialHistory hH E bonus initial fallback path).get j).1.1.val = j.val % H := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)
  have he : onlineTranscriptRowsConsistent choose [] := by simp [onlineTranscriptRowsConsistent]
  have hr := onlineSequentialPathHistory_rows_consistent choose (K*H) [] he path
  have hh := hr j
  have ht : ((qLearningActualSequentialHistory hH E bonus initial fallback path).take j.val).length = j.val := by
    simp [List.length_take, Nat.min_eq_left j.isLt.le]
  simpa [qLearningActualSequentialHistory, choose, onlineEpisodicChoose, ht] using congrArg (fun row => row.1.val) hh

/-- Later-stage table values are unchanged while the current episode executes
earlier stages, provided the slice consists of its actual chronological records. -/
theorem qLearningActualWithinEpisode_value {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (h : Fin H) (s : State) :
    qLearningChronologicalValue hH E
      (qLearningActualTableAt hH E bonus initial fallback path (k.val*H+h.val)) (h.val+1) s =
    qLearningChronologicalValue hH E
      (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)) (h.val+1) s := by
  classical
  let history := qLearningActualSequentialHistory hH E bonus initial fallback path
  let before := history.take (k.val*H)
  let slice := (history.drop (k.val*H)).take h.val
  have hlen : history.length = K*H := by
    simp [history, qLearningActualSequentialHistory, onlineSequentialPathHistory_length]
  have hstages : ∀ x ∈ slice, x.1.1.val < h.val+1 := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < h.val := by
      have := hi
      simp only [slice, List.length_take, List.length_drop] at this
      omega
    have hj : k.val*H+i < history.length := by
      rw [hlen]
      have hk : (k.val+1)*H ≤ K*H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
      have hiH : i < H := lt_trans hi' h.isLt
      have hlocal : k.val*H+i < (k.val+1)*H := by nlinarith
      omega
    have helem : x = history[k.val*H+i] := by
      simpa [slice, List.getElem_take, List.getElem_drop, Nat.add_comm] using hxi.symm
    rw [helem]
    have hs := qLearningActualSequentialHistory_stage hH E bonus initial fallback path ⟨k.val*H+i,hj⟩
    have hm : (k.val*H+i)%H = i := by simp [Nat.add_mod, Nat.mod_eq_of_lt (lt_trans hi' h.isLt)]
    have hs' : (history.get ⟨k.val*H+i,hj⟩).1.1.val = i := by
      simpa [history, hm] using hs
    have hz : i < h.val+1 := by omega
    change (history.get ⟨k.val*H+i,hj⟩).1.1.val < h.val+1
    rw [hs']
    exact hz
  have hsplit : history.take (k.val*H+h.val) = before ++ slice := by
    simp [before, slice, List.take_add]
  have hfold : qLearningActualTableAt hH E bonus initial fallback path (k.val*H+h.val) =
      qLearningChronologicalFold hH E bonus
        (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)) slice := by
    simp [qLearningActualTableAt, history, hsplit, qLearningChronologicalFold, List.foldl_append, before]
  rw [hfold]
  exact qLearningChronologicalFold_later_value hH E bonus _ slice (h.val+1) hstages s

end StatisticalRL.OnlineRL

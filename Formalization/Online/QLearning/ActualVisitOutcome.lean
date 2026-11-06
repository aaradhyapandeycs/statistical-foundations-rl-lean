import Formalization.Online.QLearning.MatchedRecordOutcome

/-! Exact successor alignment for the increasing actual visit episode list. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearning_actualVisitOutcome_eq_rowPrefix {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H)
    (i : Fin (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length) :
    let e := (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).get i
    let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
    (onlineRowOutcomes hist r).getD i.val fallback =
      (hist.map Prod.snd).getD (e*H+r.1.val) fallback := by
  classical
  let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
  let e := visits.get i
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let j := e*H+r.1.val
  have he : e < K := lt_trans ((qLearningActualVisitEpisode_get_mem hH E bonus initial fallback path k r i).1) k.isLt
  have hlen : hist.length = K*H := by simp [hist,qLearningActualSequentialHistory,onlineSequentialPathHistory_length]
  have hj : j < hist.length := by
    rw [hlen]
    dsimp [j]
    have hh := r.1.isLt
    nlinarith
  have hv := (qLearningActualVisitEpisode_get_mem hH E bonus initial fallback path k r i).2
  have hrow : hist[j].1 = r := by
    have ha := onlineTranscriptRowSequence_agrees
      ((onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)) []) hist ⟨j,hj⟩
    exact ha.symm.trans hv
  have hrank := qLearningActualVisitEpisode_rank hH E bonus initial fallback path k r i
  change (qLearningActualTableAt hH E bonus initial fallback path (e*H)).count r = i.val at hrank
  have hbefore := qLearningActualBeforeStage_count hH E bonus initial fallback path ⟨e,he⟩ r
  have hcount : (onlineRowOutcomes (hist.take j) r).length = i.val := by
    have h := hbefore.trans hrank
    simpa [j,hist,qLearningActualTableAt,qLearningChronologicalFold_count,
      qLearningChronologicalInitial,qLearningRowVisits_length_eq_outcomes] using h
  have hm := qLearning_matchedRecord_rowOutcome hist r j hj hrow fallback
  rw [hcount] at hm
  have hmap : (hist.map Prod.snd).getD j fallback = hist[j].2 := by
    rw [List.getD_eq_get _ fallback ⟨j,by simpa using hj⟩]
    simp [List.get_eq_getElem,hj]
  change (onlineRowOutcomes hist r).getD i.val fallback = (hist.map Prod.snd).getD j fallback
  rw [hmap]
  exact hm
end StatisticalRL.OnlineRL

import Formalization.Online.QLearning.SourceEpisodeNoiseConfidence

/-! Every actual target entry is indexed by the corresponding genuine visit. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearning_episodeTargets_eq_map {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    qLearningActualEpisodeTargets hH E bonus initial fallback path k r =
      (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).map
        (fun e => if he : e < K then qLearningEpisodeTargetAt hH E bonus initial fallback path r ⟨e,he⟩ else 0) := by
  classical
  unfold qLearningActualEpisodeTargets
  apply List.filterMap_eq_map_iff_forall_eq_some.mpr
  intro e he
  have he' := (qLearningActualVisitEpisodes_mem hH E bonus initial fallback path k r e).1 he
  have heK : e < K := he'.1.trans k.isLt
  simp [heK]

theorem qLearning_episodeTargets_length {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    (qLearningActualEpisodeTargets hH E bonus initial fallback path k r).length =
      (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length := by
  rw [qLearning_episodeTargets_eq_map]
  simp

theorem qLearning_episodeTargets_getD {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H)
    (i : Fin (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length) :
    let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
    let e := visits.get i
    let he : e < K := ((qLearningActualVisitEpisode_get_mem hH E bonus initial fallback path k r i).1).trans k.isLt
    (qLearningActualEpisodeTargets hH E bonus initial fallback path k r).getD i.val 0 =
      qLearningEpisodeTargetAt hH E bonus initial fallback path r ⟨e,he⟩ := by
  classical
  let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
  let e := visits.get i
  have heK : e < K := ((qLearningActualVisitEpisode_get_mem hH E bonus initial fallback path k r i).1).trans k.isLt
  rw [qLearning_episodeTargets_eq_map]
  have hi : i.val < (visits.map (fun e => if he : e < K then qLearningEpisodeTargetAt hH E bonus initial fallback path r ⟨e,he⟩ else 0)).length := by simp [visits,i.isLt]
  rw [List.getD_eq_get _ 0 ⟨i.val,hi⟩]
  have heK' : (qLearningActualVisitEpisodes hH E bonus initial fallback path k r)[i.val] < K := by
    simpa [e,visits,List.get_eq_getElem] using heK
  simp [List.get_eq_getElem,visits,heK']
end StatisticalRL.OnlineRL

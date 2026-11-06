import Formalization.Online.QLearning.EpisodeList

/-! deterministic source bridge. It consumes the actual
sequential target-log identity, not a user-supplied recurrence or certificate. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Actual pre-episode Q is the source weighted sum over targets from earlier
visit episodes, in strictly increasing chronological order. Each target uses
the corresponding actual pre-episode continuation and observed successor. -/
theorem qLearningActualEpisode_weighted {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    let targets := qLearningActualEpisodeTargets hH E bonus initial fallback path k r
    (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r =
      onlineQRateWeight H targets.length 0 * H +
        ∑ i ∈ Finset.Icc 1 targets.length,
          onlineQRateWeight H targets.length i * targets.getD (i-1) 0 := by
  have h := qLearningActualTableAt_weighted hH E bonus initial fallback path (k.val*H) r
  have hlog := qLearningActualTargetListIdentity_holds (State := State) (Action := Action)
    hH E bonus initial fallback path k r
  dsimp only at h ⊢
  rw [hlog] at h
  exact h

/-- The i-th ordered visit index denotes a genuine earlier episode and its
actual row matches r. This theorem does not yet identify i with the row count. -/
theorem qLearningActualVisitEpisode_get_mem {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H)
    (i : Fin (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length) :
    let e := (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).get i
    e < k.val ∧
      onlineTranscriptRowSequence
        ((onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)) [])
        (qLearningActualSequentialHistory hH E bonus initial fallback path)
        (e*H+r.1.val) = r := by
  exact (qLearningActualVisitEpisodes_mem hH E bonus initial fallback path k r _).1
    (List.get_mem _ _)

end StatisticalRL.OnlineRL

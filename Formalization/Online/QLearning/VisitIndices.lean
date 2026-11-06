import Formalization.Online.QLearning.ActualEpisode
import Formalization.Online.QLearning.ActualVisitDefinitions
import Formalization.Online.Regret.W1.OnlineW1ActualEpisodeCount
import Mathlib.Data.List.Sort

/-! source bridge. Episode indices are extracted from the
actual sequential transcript; no visit independence or concentration is assumed. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- Visit indices are strictly increasing; no repeated episode is possible. -/
theorem qLearningActualVisitEpisodes_strict {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).Pairwise (· < ·) := by
  classical
  unfold qLearningActualVisitEpisodes
  exact (List.pairwise_lt_range (n := k.val)).filter _

/-- Each element is genuinely an earlier episode whose row at r's stage is r. -/
theorem qLearningActualVisitEpisodes_mem {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) (e : ℕ) :
    e ∈ qLearningActualVisitEpisodes hH E bonus initial fallback path k r ↔
      e < k.val ∧
        onlineTranscriptRowSequence
          ((onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)) [])
          (qLearningActualSequentialHistory hH E bonus initial fallback path)
          (e*H+r.1.val) = r := by
  classical
  simp [qLearningActualVisitEpisodes]

/-- Filtered transcript row records and row outcome lists have equal length. -/
lemma qLearningRowVisits_length_eq_outcomes {H : ℕ}
    (hist : List (OnlineMDPRow State Action H × State)) (r : OnlineMDPRow State Action H) :
    (qLearningRowVisits r hist).length = (onlineRowOutcomes hist r).length := by
  classical
  induction hist with
  | nil => simp [qLearningRowVisits, onlineRowOutcomes]
  | cons x xs ih =>
      simp only [qLearningRowVisits, onlineRowOutcomes] at ih
      by_cases hx : x.1 = r <;> simp [qLearningRowVisits, onlineRowOutcomes, hx, ih]

/-- Generic filtered range length agrees with the project's visit count. -/
lemma qLearningRangeVisits_length {Row : Type*} (rowAt : ℕ → Row) (k : ℕ) (r : Row) :
    ((List.range k).filter (fun e => rowAt e = r)).length = onlineVisitCount rowAt k r := by
  classical
  induction k with
  | zero => simp [onlineVisitCount]
  | succ k ih =>
      rw [List.range_succ, List.filter_append, onlineVisitCount_succ]
      by_cases h : rowAt k = r <;> simp [h, ih]

/-- Actual pre-episode table count equals the length of the ordered episode
visit list, and also the actual pre-update target-log length. -/
theorem qLearningActualVisitEpisodes_length {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length =
      (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).count r ∧
    (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length =
      (qLearningLoggedVisitFold hH E bonus r (qLearningChronologicalInitial H)
        ((qLearningActualSequentialHistory hH E bonus initial fallback path).take (k.val*H))).2.length := by
  classical
  let planner := qLearningActualEpisodePlanner hH E bonus
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := qLearningActualSequentialHistory hH E bonus initial fallback path
  let rowAt := onlineTranscriptRowSequence (choose []) history
  have hcount := onlineSequential_observedCount_eq_stageVisitRank H K hH E initial fallback
    planner path k r.1 r rfl
  have hlen : (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length =
      (onlineRowOutcomes (history.take (k.val*H)) r).length := by
    rw [show (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length =
        onlineVisitCount (fun e => rowAt (e*H+r.1.val)) k.val r by
      unfold qLearningActualVisitEpisodes
      convert qLearningRangeVisits_length (fun e => rowAt (e*H+r.1.val)) k.val r using 1 <;>
        simp only [planner, choose, history, rowAt]
      apply congrArg List.length
      apply List.filter_congr
      intro x hx
      simp]
    simpa [planner, choose, history, rowAt, qLearningActualSequentialHistory] using hcount.symm
  have hrow := qLearningRowVisits_length_eq_outcomes (history.take (k.val*H)) r
  constructor
  · rw [qLearningActualTableAt, qLearningChronologicalFold_count]
    simpa [qLearningChronologicalInitial, history, hrow] using hlen
  · rw [qLearningLogged_length]
    simpa [history, hrow] using hlen

end StatisticalRL.OnlineRL

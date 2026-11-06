import Formalization.Online.QLearning.VisitRank
import Formalization.Online.QLearning.ActualBlock

/-! Private actual visit-rank and bonus identification; no stochastic claim. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- The queried row has the same count before its stage as at episode start,
because all prior stages have different stage tags. -/
theorem qLearningActualBeforeStage_count {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (e : Fin K) (r : OnlineMDPRow State Action H) :
    (qLearningActualTableAt hH E bonus initial fallback path (e.val*H+r.1.val)).count r =
      (qLearningActualTableAt hH E bonus initial fallback path (e.val*H)).count r := by
  classical
  rw [← qLearningActualBlockBefore_table]
  rw [qLearningChronologicalFold_count]
  have hempty : qLearningRowVisits r (qLearningActualBlockBefore hH E bonus initial fallback path e r.1) = [] := by
    unfold qLearningRowVisits
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp [qLearningActualBlockBefore_noVisit hH E bonus initial fallback path e r x hx]
  simp [hempty]

/-- The actual i-th earlier visit uses source count i+1, both in learning rate
and bonus, and its target uses the actual pre-episode continuation. -/
theorem qLearningActualEpisodeTarget_ranked {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H)
    (i : Fin (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length) :
    let e := (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).get i
    let he : e < K := lt_trans ((qLearningActualVisitEpisode_get_mem hH E bonus initial fallback path k r i).1) k.isLt
    let history := qLearningActualSequentialHistory hH E bonus initial fallback path
    qLearningEpisodeTargetAt hH E bonus initial fallback path r ⟨e,he⟩ =
      (E r.1).reward r.2.1 r.2.2 +
        qLearningChronologicalValue hH E
          (qLearningActualTableAt hH E bonus initial fallback path (e*H))
          (r.1.val+1) ((history.map Prod.snd).getD (e*H+r.1.val) fallback) + bonus (i.val+1) := by
  classical
  let visits := qLearningActualVisitEpisodes hH E bonus initial fallback path k r
  let e := visits.get i
  have he : e < K := lt_trans ((qLearningActualVisitEpisode_get_mem hH E bonus initial fallback path k r i).1) k.isLt
  have hrank := qLearningActualVisitEpisode_rank hH E bonus initial fallback path k r i
  change (qLearningActualTableAt hH E bonus initial fallback path (e*H)).count r = i.val at hrank
  have hbefore := qLearningActualBeforeStage_count hH E bonus initial fallback path ⟨e,he⟩ r
  simp only [qLearningEpisodeTargetAt]
  rw [hbefore, hrank]

end StatisticalRL.OnlineRL

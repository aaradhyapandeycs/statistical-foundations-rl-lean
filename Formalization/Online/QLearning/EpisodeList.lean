import Formalization.Online.QLearning.ActualBlockStep
import Formalization.Online.QLearning.EpisodeListTarget

/-! actual episode-log induction. No event, recurrence, or
list-equality certificate is an input. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- The table after earlier stages of episode e is the actual prefix table
immediately before its stage-h record. -/
theorem qLearningActualBlockBefore_table {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (e : Fin K) (h : Fin H) :
    qLearningChronologicalFold hH E bonus
      (qLearningActualTableAt hH E bonus initial fallback path (e.val*H))
      (qLearningActualBlockBefore hH E bonus initial fallback path e h) =
    qLearningActualTableAt hH E bonus initial fallback path (e.val*H+h.val) := by
  classical
  simp [qLearningActualTableAt, qLearningActualBlockBefore,
    qLearningChronologicalFold, List.foldl_append, List.take_add]

/-- The selected stage record is the row sequence at the source episode/stage. -/
theorem qLearningActualBlockRecord_row {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (e : Fin K) (h : Fin H) :
    (qLearningActualBlockRecord hH E bonus initial fallback path e h).1 =
      onlineTranscriptRowSequence
        ((onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)) [])
        (qLearningActualSequentialHistory hH E bonus initial fallback path) (e.val*H+h.val) := by
  classical
  unfold qLearningActualBlockRecord
  exact (onlineTranscriptRowSequence_agrees _ _ _).symm

/-- On a matching actual visit, the block target equals the source
pre-episode continuation target. -/
theorem qLearningActualBlockRecord_target {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (e : Fin K) (r : OnlineMDPRow State Action H)
    (hrow : (qLearningActualBlockRecord hH E bonus initial fallback path e r.1).1 = r) :
    qLearningVisitTarget hH E bonus
      (qLearningChronologicalFold hH E bonus
        (qLearningActualTableAt hH E bonus initial fallback path (e.val*H))
        (qLearningActualBlockBefore hH E bonus initial fallback path e r.1))
      (qLearningActualBlockRecord hH E bonus initial fallback path e r.1) =
    qLearningEpisodeTargetAt hH E bonus initial fallback path r e := by
  classical
  rw [qLearningActualBlockBefore_table]
  unfold qLearningActualBlockRecord at hrow ⊢
  apply qLearningEpisodeTargetAt_eq_actual hH E bonus initial fallback path r e
  exact hrow

/-- Episode-list target specification at arbitrary completed count n≤K. -/
noncomputable def qLearningEpisodeTargetsBefore {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (n : ℕ) (r : OnlineMDPRow State Action H) : List ℝ := by
  classical
  exact (List.range n).filterMap (fun e =>
    if he : e < K then
      if (qLearningActualBlockRecord hH E bonus initial fallback path ⟨e,he⟩ r.1).1 = r then
        some (qLearningEpisodeTargetAt hH E bonus initial fallback path r ⟨e,he⟩)
      else none
    else none)

/-- Full actual chronological log equals the increasing list of episode
visit targets, including the real pre-episode continuations. -/
theorem qLearningActualEpisodeLog_eq_targets {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (n : ℕ) (hn : n ≤ K) (r : OnlineMDPRow State Action H) :
    qLearningActualEpisodeLog hH E bonus initial fallback path n r =
      qLearningEpisodeTargetsBefore hH E bonus initial fallback path n r := by
  classical
  induction n with
  | zero => simp [qLearningActualEpisodeLog, qLearningEpisodeTargetsBefore, qLearningLoggedVisitFold]
  | succ n ih =>
      have hn' : n ≤ K := by omega
      have hnK : n < K := by omega
      have hstep := qLearningActualEpisodeLog_succ hH E bonus initial fallback path ⟨n,hnK⟩ r
      rw [hstep, ih hn']
      simp only [qLearningEpisodeTargetsBefore, List.range_succ, List.filterMap_append]
      by_cases hrow : (qLearningActualBlockRecord hH E bonus initial fallback path ⟨n,hnK⟩ r.1).1 = r
      · simp [hnK, hrow, qLearningActualBlockRecord_target hH E bonus initial fallback path ⟨n,hnK⟩ r hrow]
      · simp [hnK, hrow]

/-- Filtering then mapping agrees with a single conditional filterMap. -/
private theorem qLearning_filterMap_filter {α β : Type*} (l : List α)
    (p : α → Bool) (f : α → Option β) :
    (l.filter p).filterMap f = l.filterMap (fun x => if p x then f x else none) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      cases hp : p x <;> cases hf : f x <;> simp [hp, hf, ih]

/-- The operational episode-target list is exactly the earlier sorted visit
index representation, with no extra selection or count premise. -/
theorem qLearningEpisodeTargetsBefore_eq_visits {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) :
    qLearningEpisodeTargetsBefore hH E bonus initial fallback path k.val r =
      qLearningActualEpisodeTargets hH E bonus initial fallback path k r := by
  classical
  unfold qLearningEpisodeTargetsBefore qLearningActualEpisodeTargets qLearningActualVisitEpisodes
  rw [qLearning_filterMap_filter]
  apply List.filterMap_congr
  intro e he
  have heK : e < K := lt_trans (List.mem_range.mp he) k.isLt
  have hr := qLearningActualBlockRecord_row hH E bonus initial fallback path ⟨e,heK⟩ r.1
  simp only [heK, dite_true]
  rw [← hr]
  by_cases hm : (qLearningActualBlockRecord hH E bonus initial fallback path ⟨e,heK⟩ r.1).1 = r <;>
    simp [hm]

/-- The actual pre-episode target log equals the source's increasing sequence
of visit-episode targets, with the actual pre-episode continuation at each. -/
theorem qLearningActualTargetListIdentity_holds :
    qLearningActualTargetListIdentity (State := State) (Action := Action) := by
  intro H K hH E bonus initial fallback path k r
  change qLearningActualEpisodeLog hH E bonus initial fallback path k.val r = _
  rw [qLearningActualEpisodeLog_eq_targets hH E bonus initial fallback path k.val k.isLt.le r,
    qLearningEpisodeTargetsBefore_eq_visits]

end StatisticalRL.OnlineRL

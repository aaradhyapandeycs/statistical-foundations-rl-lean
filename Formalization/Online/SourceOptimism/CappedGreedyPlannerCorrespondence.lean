import Formalization.Online.SourceOptimism.ObservedBackwardOptimismComposition

/-! A deterministic greedy episode planner from the
same corrected capped table, plus initialization and completed-update identities.
Source episode k+1 is zero-based k. This does not claim law/probability closure. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- The completed-history table computed after an episode, before the next
policy is chosen. Stage order is the source chronological order. -/
noncomputable def onlineCompletedHistoryPlanningStages {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) :
    List (OnlineObservedPlanningStage State Action) :=
  List.ofFn (fun h => onlineHistoryPlanningStage E history h)

/-- A fixed deterministic maximizing tie rule. It depends only on the supplied
completed history and the current stage/state, never on new episode samples. -/
noncomputable def onlineCappedGreedyPlanner {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (L c₁ c₂ : ℝ) :
    OnlineEpisodePlanner State Action H :=
  fun history h s =>
    letI : Nonempty Action := (E h).action_nonempty
    Classical.choose (EnvironmentStage.exists_maximizer
      (onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
        (onlineCompletedHistoryPlanningStages E history) h.val s))

/-- The selected action actually maximizes this same data-dependent Q table. -/
theorem onlineCappedGreedyPlanner_max {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (L c₁ c₂ : ℝ)
    (history : List (OnlineMDPRow State Action H × State)) (h : Fin H) (s : State) :
    letI : Nonempty Action := (E h).action_nonempty
    onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
        (onlineCompletedHistoryPlanningStages E history) h.val s
        (onlineCappedGreedyPlanner E L c₁ c₂ history h s) =
      actionMaximum (onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
        (onlineCompletedHistoryPlanningStages E history) h.val s) := by
  letI : Nonempty Action := (E h).action_nonempty
  exact Classical.choose_spec (EnvironmentStage.exists_maximizer _)

/-- At a completed episode boundary, taking the first k*H transitions leaves
exactly this history; the planner's input and its pre-episode table agree. -/
theorem onlinePreEpisodePlanningStages_eq_completed {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ)
    (hlen : history.length = k * H) :
    onlinePreEpisodePlanningStages E history k =
      onlineCompletedHistoryPlanningStages E history := by
  have htake : history.take (k * H) = history := by
    rw [← hlen, List.take_length]
  simp only [onlinePreEpisodePlanningStages, onlineCompletedHistoryPlanningStages, htake]

/-- The exact Q table used to choose the policy in source episode k+1 is its
pre-episode table, with no additional recomputation on different observations. -/
theorem onlineCappedGreedyPlanner_preEpisode_max {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (L c₁ c₂ : ℝ)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ)
    (hlen : history.length = k * H) (h : Fin H) (s : State) :
    letI : Nonempty Action := (E h).action_nonempty
    onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
        (onlinePreEpisodePlanningStages E history k) h.val s
        (onlineCappedGreedyPlanner E L c₁ c₂ history h s) =
      actionMaximum (onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
        (onlinePreEpisodePlanningStages E history k) h.val s) := by
  rw [onlinePreEpisodePlanningStages_eq_completed E history k hlen]
  exact onlineCappedGreedyPlanner_max E L c₁ c₂ history h s

/-- Every unvisited active row has the initialized source value H. This uses
the explicit N=0 correction and evaluates no zero-count bonus. -/
theorem onlineEmptyHistory_Q_initialization {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (L c₁ c₂ : ℝ)
    (h : Fin H) (s : State) (a : Action) :
    onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
      (onlineCompletedHistoryPlanningStages E []) h.val s a = (H : ℝ) := by
  have hdrop := onlinePreEpisodePlanningStages_drop_stage E [] 0 h
  have htable : onlinePreEpisodePlanningStages E [] 0 =
      onlineCompletedHistoryPlanningStages E [] := by
    exact onlinePreEpisodePlanningStages_eq_completed E [] 0 (by simp)
  rw [htable] at hdrop
  unfold onlineCappedBackwardQAt
  rw [hdrop]
  apply onlineCappedStageQ_zero_count
  simp [onlineHistoryPlanningStage, onlineRowOutcomes]

/-- Empty-history active V initialization agrees with max of the H Q entries. -/
theorem onlineEmptyHistory_V_initialization {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (L c₁ c₂ : ℝ)
    (h : Fin H) (s : State) :
    onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂
      (onlineCompletedHistoryPlanningStages E []) h.val s = (H : ℝ) := by
  letI : Nonempty Action := (E h).action_nonempty
  have hdrop := onlinePreEpisodePlanningStages_drop_stage E [] 0 h
  have htable := onlinePreEpisodePlanningStages_eq_completed E [] 0 (by simp)
  rw [htable] at hdrop
  simp only [List.take_nil] at hdrop
  have hQ (a : Action) := onlineEmptyHistory_Q_initialization E L c₁ c₂ h s a
  unfold onlineCappedBackwardQAt at hQ
  rw [hdrop] at hQ
  unfold onlineCappedBackwardValueAt
  rw [hdrop]
  rw [onlineCappedBackwardValue]
  obtain ⟨a, ha⟩ := EnvironmentStage.exists_maximizer
    (onlineCappedStageQ (H : ℝ) L c₁ c₂
      (onlineHistoryPlanningStage E ([] : List (OnlineMDPRow State Action H × State)) h)
      (onlineCappedBackwardValue (H : ℝ) L c₁ c₂
        ((onlineCompletedHistoryPlanningStages E []).drop (h.val + 1))) s)
  dsimp only
  rw [← ha]
  exact hQ a

/-- Recording one complete H-step episode makes its entire updated history the
next pre-episode history. It includes the last transition's count increment. -/
theorem onlineCompletedEpisode_nextPlanningStages {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (before episode : List (OnlineMDPRow State Action H × State)) (k : ℕ)
    (hbefore : before.length = k * H) (hepisode : episode.length = H) :
    onlinePreEpisodePlanningStages E (before ++ episode) (k + 1) =
      onlineCompletedHistoryPlanningStages E (before ++ episode) := by
  apply onlinePreEpisodePlanningStages_eq_completed
  simp only [List.length_append, hbefore, hepisode, Nat.add_mul, one_mul]

/-- Source terminal continuation is zero, also at empty-data initialization. -/
theorem onlineCompletedHistory_terminalValue {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (L c₁ c₂ : ℝ)
    (history : List (OnlineMDPRow State Action H × State)) (s : State) :
    onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂
      (onlineCompletedHistoryPlanningStages E history) H s = 0 := by
  have hlength : (onlineCompletedHistoryPlanningStages E history).length = H := by
    simp [onlineCompletedHistoryPlanningStages]
  have hdrop : (onlineCompletedHistoryPlanningStages E history).drop H = [] := by
    exact List.drop_eq_nil_of_le hlength.le
  simp [onlineCappedBackwardValueAt, hdrop, onlineCappedBackwardValue]

end StatisticalRL.OnlineRL

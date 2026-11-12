import Formalization.Online.SourceOptimism.CappedGreedyPlannerDefinitions
import Formalization.Online.SourceOptimism.ObservedBackwardOptimismComposition

/-! A deterministic greedy episode planner from the
same corrected capped table, plus initialization and completed-update identities.
Source episode k+1 is zero-based k. This does not claim law/probability closure. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

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

end StatisticalRL.OnlineRL

import Formalization.Online.SourceOptimism.HistoryPlanningDefinitions

/-! Definitions of the completed-history table and deterministic greedy planner. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance onlinePlannerDefinitionDecidableState : DecidableEq State := Classical.decEq State
noncomputable local instance onlinePlannerDefinitionDecidableAction : DecidableEq Action := Classical.decEq Action

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
    Classical.choose (by
      obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
        (onlineCompletedHistoryPlanningStages E history) h.val s)
      exact ⟨a, ha.symm⟩)

end StatisticalRL.OnlineRL

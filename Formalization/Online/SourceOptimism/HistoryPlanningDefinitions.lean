import Formalization.Online.SourceOptimism.EpisodicSelectorDefinitions
import Formalization.Online.SourceOptimism.CappedPlanningDefinitions
import Formalization.Online.SourceOptimism.RowOutcomeDefinitions
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance historyDefinitionStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance historyDefinitionActionDecidable : DecidableEq Action := Classical.decEq Action
/-- One chronological stage with the actual observed row lists. -/
noncomputable def onlineHistoryPlanningStage {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (h : Fin H) :
    OnlineObservedPlanningStage State Action where
  environment := E h
  observations s a := onlineRowOutcomes history (h, (s, a))

/-- Zero-based episode k uses exactly the first k*H recorded transitions.
Source episode k+1 follows all increments of the first k completed episodes. -/
noncomputable def onlinePreEpisodePlanningStages {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State)) (k : ℕ) :
    List (OnlineObservedPlanningStage State Action) :=
  List.ofFn (fun h => onlineHistoryPlanningStage E (history.take (k * H)) h)

end StatisticalRL.OnlineRL

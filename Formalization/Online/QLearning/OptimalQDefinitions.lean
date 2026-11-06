import Formalization.Online.QLearning.OptimalNextDefinitions
import Formalization.Online.SourceOptimism.EpisodicSelectorDefinitions

namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def qLearningTrueOptimalQ {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (r : OnlineMDPRow State Action H) : ℝ :=
  (E r.1).reward r.2.1 r.2.2 +
    ((E r.1).transition r.2.1 r.2.2).expectation (qLearningTrueOptimalNext E r)


end StatisticalRL.OnlineRL

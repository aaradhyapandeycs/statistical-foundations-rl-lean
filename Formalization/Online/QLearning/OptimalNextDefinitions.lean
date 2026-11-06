import Formalization.Online.SourceOptimism.EpisodicSelectorDefinitions
import Formalization.MDP.EnvironmentDefinitions

namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def qLearningTrueOptimalNext {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (r : OnlineMDPRow State Action H) : State → ℝ :=
  EnvironmentStage.optimalValue ((List.ofFn E).drop (r.1.val+1))


end StatisticalRL.OnlineRL

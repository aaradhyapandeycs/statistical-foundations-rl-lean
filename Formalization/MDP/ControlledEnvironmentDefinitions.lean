import Formalization.MDP.EnvironmentDefinitions
import Formalization.MDP.DecisionStageDefinitions
namespace StatisticalRL.EnvironmentStage
variable {State Action : Type*} [Fintype State] [Fintype Action]
/-- Attach a decision rule without changing the environment. -/
def withPolicy (e : EnvironmentStage State Action) (π : StationaryPolicy State Action) :
    DecisionStage State Action where
  state_nonempty := e.state_nonempty
  action_nonempty := e.action_nonempty
  transition := e.transition
  reward := e.reward
  reward_nonneg := e.reward_nonneg
  reward_le_one := e.reward_le_one
  policy := π


end StatisticalRL.EnvironmentStage

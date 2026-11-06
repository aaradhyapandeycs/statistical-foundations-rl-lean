import Formalization.MDP.CoreDefinitions

namespace StatisticalRL

/-- One nonstationary finite-horizon stage together with its randomized decision rule. -/
structure DecisionStage (State Action : Type*) [Fintype State] [Fintype Action] where
  state_nonempty : Nonempty State
  action_nonempty : Nonempty Action
  transition : State → Action → FiniteDistribution State
  reward : State → Action → ℝ
  reward_nonneg : ∀ s a, 0 ≤ reward s a
  reward_le_one : ∀ s a, reward s a ≤ 1
  policy : StationaryPolicy State Action

namespace DecisionStage

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The action-value backup of a specified continuation value. -/
def qBackup (stage : DecisionStage State Action) (V : State → ℝ)
    (s : State) (a : Action) : ℝ :=
  stage.reward s a + (stage.transition s a).expectation V

/-- Policy averaging of the action-value backup. -/
def valueBackup (stage : DecisionStage State Action) (V : State → ℝ) (s : State) : ℝ :=
  (stage.policy s).expectation (stage.qBackup V s)


end DecisionStage
end StatisticalRL

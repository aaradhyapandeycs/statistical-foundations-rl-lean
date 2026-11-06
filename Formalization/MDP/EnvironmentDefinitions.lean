import Formalization.MDP.CoreDefinitions
import Formalization.MDP.OptimalityOperatorDefinitions

namespace StatisticalRL

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- One time step of an environment, before any policy is selected. -/
structure EnvironmentStage (State Action : Type*) [Fintype State] [Fintype Action] where
  state_nonempty : Nonempty State
  action_nonempty : Nonempty Action
  transition : State → Action → FiniteDistribution State
  reward : State → Action → ℝ
  reward_nonneg : ∀ s a, 0 ≤ reward s a
  reward_le_one : ∀ s a, reward s a ≤ 1


namespace EnvironmentStage

/-- Expected one-step reward and continuation in the policy-independent model. -/
def qBackup (e : EnvironmentStage State Action) (V : State → ℝ)
    (s : State) (a : Action) : ℝ :=
  e.reward s a + (e.transition s a).expectation V

/-- Optimal continuation value, defined by backward induction. -/
noncomputable def optimalValue : List (EnvironmentStage State Action) → State → ℝ
  | [] => fun _ ↦ 0
  | e :: es => fun s ↦
    letI : Nonempty Action := e.action_nonempty
    actionMaximum (e.qBackup (optimalValue es) s)

/-- Optimal action-value, including the source's zero terminal convention. -/
noncomputable def optimalQ : List (EnvironmentStage State Action) → State → Action → ℝ
  | [] => fun _ _ ↦ 0
  | e :: es => e.qBackup (optimalValue es)

end EnvironmentStage

end StatisticalRL

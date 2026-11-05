import Formalization.MDP.CoreDefinitions

namespace StatisticalRL.EnvironmentStage
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The probability vector concentrated on a specified action. -/
noncomputable def pointMass (a : Action) : FiniteDistribution Action := by
  classical
  exact ⟨fun b ↦ if b = a then 1 else 0,
    fun b ↦ by dsimp; split <;> norm_num,
    by simp⟩

end StatisticalRL.EnvironmentStage

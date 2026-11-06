import Formalization.MDP.ControlledEnvironmentDefinitions
import Formalization.MDP.PointMassDefinitions
namespace StatisticalRL.EnvironmentStage
variable {State Action : Type*} [Fintype State] [Fintype Action]
/-- An actual nonstationary randomized policy indexed from the current stage. -/
def controlled : List (EnvironmentStage State Action) →
    (ℕ → StationaryPolicy State Action) → List (DecisionStage State Action)
  | [], _ => []
  | e :: es, π => e.withPolicy (π 0) :: controlled es (fun n ↦ π (n + 1))

/-- A maximizing action in each state of a stage. -/
noncomputable def greedyAction (e : EnvironmentStage State Action)
    (V : State → ℝ) (s : State) : Action := by
  letI : Nonempty Action := e.action_nonempty
  exact Classical.choose (by
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (e.qBackup V s)
    exact ⟨a, ha.symm⟩)

/-- The greedy policy at each stage depends on that stage's optimal continuation. -/
noncomputable def greedyStages : List (EnvironmentStage State Action) →
    List (DecisionStage State Action)
  | [] => []
  | e :: es => e.withPolicy (fun s ↦ pointMass (e.greedyAction (optimalValue es) s)) ::
      greedyStages es


end StatisticalRL.EnvironmentStage

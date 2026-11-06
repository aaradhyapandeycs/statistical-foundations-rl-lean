import Formalization.MDP.ControlledEnvironmentDefinitions
import Formalization.MDP.PointMassDefinitions
import Formalization.MDP.TrajectoryDefinitions
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
/-- The same environment controlled by a fixed deterministic stage policy. -/
noncomputable def onlineFixedPolicyStages {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (g : Fin H → State → Action) :
    List (DecisionStage State Action) :=
  List.ofFn (fun h => (E h).withPolicy (fun s => EnvironmentStage.pointMass (g h s)))


end StatisticalRL.OnlineRL

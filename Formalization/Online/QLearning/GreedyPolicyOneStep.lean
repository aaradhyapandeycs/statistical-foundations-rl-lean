import Formalization.Online.QLearning.ActualGreedyChoice
import Formalization.Online.Regret.T4.OnlineRegretT4Telescope

/-! One-step comparison with the actual fixed greedy policy's true trajectory value. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem qLearning_greedyPolicy_oneStep {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (h : Fin H) (s : State) :
    let g := qLearningChronologicalPolicy E table
    let a := g h s
    let r : OnlineMDPRow State Action H := (h,(s,a))
    let D := onlineFixedPolicyStages E g
    qLearningChronologicalValue hH E table h.val s - DecisionStage.trajectoryValue (D.drop h.val) s ≤
      table.q r - qLearningTrueOptimalQ E r +
        (onlineMDPSuccessorRowLaw E r).expectation
          (fun x => qLearningTrueOptimalNext E r x - DecisionStage.trajectoryValue (D.drop (h.val+1)) x) := by
  classical
  let g := qLearningChronologicalPolicy E table
  let a := g h s
  let r : OnlineMDPRow State Action H := (h,(s,a))
  let D := onlineFixedPolicyStages E g
  have hv := qLearningChronologicalValue_le_greedyQ hH E table h s
  have hp := onlineFixedPolicyValue_step E g h s
  change qLearningChronologicalValue hH E table h.val s - DecisionStage.trajectoryValue (D.drop h.val) s ≤
      table.q r - qLearningTrueOptimalQ E r +
        (onlineMDPSuccessorRowLaw E r).expectation
          (fun x => qLearningTrueOptimalNext E r x - DecisionStage.trajectoryValue (D.drop (h.val+1)) x)
  rw [FiniteDistribution.expectation_sub]
  dsimp only [qLearningTrueOptimalQ,onlineMDPSuccessorRowLaw,r,a,g] at *
  linarith
end StatisticalRL.OnlineRL

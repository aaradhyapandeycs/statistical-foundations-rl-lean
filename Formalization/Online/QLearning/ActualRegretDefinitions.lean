import Formalization.Online.QLearning.ActualEpisodeDefinitions
import Formalization.Online.SourceOptimism.FixedPolicyDefinitions
open scoped BigOperators
namespace StatisticalRL.OnlineRL
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
/-- True trajectory value of the actual greedy policy frozen from this table. -/
noncomputable def qLearningGreedyTruePolicyValue {H : ℕ}
    (E : Fin H → EnvironmentStage State Action)
    (table : QLearningChronologicalTable (State := State) (Action := Action) H)
    (n : ℕ) (s : State) : ℝ :=
  DecisionStage.trajectoryValue
    ((onlineFixedPolicyStages E (qLearningChronologicalPolicy E table)).drop n) s

/-- Actual source pseudo-regret, evaluated with each selected policy's true
trajectory value in the unchanged environment. -/
noncomputable def qLearningActualRegret {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H)) : ℝ :=
  ∑ k : Fin K,
    let table := qLearningActualTableAt hH E bonus initial fallback path (k.val*H)
    EnvironmentStage.optimalValue (List.ofFn E) (initial k) -
      qLearningGreedyTruePolicyValue E table 0 (initial k)


end StatisticalRL.OnlineRL

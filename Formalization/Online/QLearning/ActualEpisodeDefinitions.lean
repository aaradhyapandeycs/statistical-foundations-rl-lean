import Formalization.Online.QLearning.ChronologicalDefinitions
import Formalization.Online.SourceOptimism.EpisodicSelectorDefinitions
import Formalization.MDP.FinitePathHistoryDefinitions

namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- Actual episode policy is selected from the fold of completed history. -/
noncomputable def qLearningActualEpisodePlanner {H : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ) :
    OnlineEpisodePlanner State Action H :=
  fun history => qLearningChronologicalPolicy E
    (qLearningChronologicalFold hH E bonus (qLearningChronologicalInitial H) history)

/-- Transcript induced by the actual reset vector and sequential sample path. -/
noncomputable def qLearningActualSequentialHistory {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H)) :=
  onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus))
    (K*H) [] path

/-- The actual Q table before an episode or stage. -/
noncomputable def qLearningActualTableAt {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H)) (n : ℕ) :=
  qLearningChronologicalFold hH E bonus (qLearningChronologicalInitial H)
    ((qLearningActualSequentialHistory hH E bonus initial fallback path).take n)


end StatisticalRL.OnlineRL

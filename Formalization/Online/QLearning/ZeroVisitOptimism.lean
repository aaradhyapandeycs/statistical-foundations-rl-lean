import Formalization.Online.QLearning.ValueOptimism

/-! Actual Q-learning table remains initialized at an unvisited row. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

theorem qLearning_actualZeroVisit_q {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H)
    (ht : (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length = 0) :
    (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r = H := by
  have hw := qLearningActualEpisode_weighted hH E bonus initial fallback path k r
  have htarget : (qLearningActualEpisodeTargets hH E bonus initial fallback path k r).length = 0 := by
    rw [qLearning_episodeTargets_length,ht]
  dsimp only at hw
  rw [htarget] at hw
  simpa [qLearning_rate_zero_eq hH] using hw

theorem qLearning_actualZeroVisit_optimistic {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{u,0} State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H)
    (ht : (qLearningActualVisitEpisodes hH E bonus initial fallback path k r).length = 0) :
    0 ≤ (qLearningActualTableAt hH E bonus initial fallback path (k.val*H)).q r - qLearningTrueOptimalQ E r := by
  rw [qLearning_actualZeroVisit_q hH E bonus initial fallback path k r ht]
  have h := (qLearningTrueOptimalQ_mem_Icc E r).2
  linarith
end StatisticalRL.OnlineRL

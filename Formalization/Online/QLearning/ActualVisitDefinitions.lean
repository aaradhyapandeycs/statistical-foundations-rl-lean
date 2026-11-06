import Formalization.Online.QLearning.ActualEpisodeDefinitions
import Formalization.Online.SourceOptimism.TranscriptRowDefinitions

namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
attribute [local instance] Classical.propDecidable

/-- Increasing earlier episode indices visiting r at its stage. -/
noncomputable def qLearningActualVisitEpisodes {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (k : Fin K) (r : OnlineMDPRow State Action H) : List ℕ := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback (qLearningActualEpisodePlanner hH E bonus)
  let hist := qLearningActualSequentialHistory hH E bonus initial fallback path
  let rowAt := onlineTranscriptRowSequence (choose []) hist
  exact (List.range k.val).filter (fun e => rowAt (e*H+r.1.val)=r)


end StatisticalRL.OnlineRL

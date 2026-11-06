import Formalization.Online.QLearning.ActualLaw
import Formalization.Online.Regret.MVP.Model.OnlineMVPActualSampler

/-! Private deterministic specialization of the arbitrary-planner stack sampler. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance qLearningStackRowsStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance qLearningStackRowsActionDecidable : DecidableEq Action := Classical.decEq Action

/-- At most one observation of a fixed stage-tagged row occurs per episode. -/
theorem qLearning_stack_rowCount_le {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (n : ℕ) (hn : n ≤ K*H) (r : OnlineMDPRow State Action H) :
    (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback
      (qLearningActualEpisodePlanner hH E bonus) data n) r).length ≤ K := by
  exact onlineMVPActualStackHistory_rowCount_le_K hH initial fallback
    (qLearningActualEpisodePlanner hH E bonus) data n hn r

/-- The zero-based i-th observed outcome of a row is exactly its i-th stack
coordinate, with the coordinate bound obtained from the stage clock. -/
theorem qLearning_stack_rowNth_eq {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (n : ℕ) (hn : n ≤ K*H) (r : OnlineMDPRow State Action H)
    (i : Fin (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback
      (qLearningActualEpisodePlanner hH E bonus) data n) r).length) :
    (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback
      (qLearningActualEpisodePlanner hH E bonus) data n) r).get i =
      data (r, ⟨i.val, by
        have hc := qLearning_stack_rowCount_le hH E bonus initial fallback data n hn r
        omega⟩) := by
  exact onlineMVPActualStackHistory_rowNth_eq_stack hH initial fallback
    (qLearningActualEpisodePlanner hH E bonus) data n hn r i
end StatisticalRL.OnlineRL

import Formalization.Online.QLearning.ActualStackRateUnion
import Formalization.Online.QLearning.OptimalNextDefinitions
import Formalization.Online.SourceOptimism.CappedBackwardOptimism

/-! Actual finite-horizon optimal successor values satisfy the global H cap. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem qLearningTrueOptimalNext_mem_Icc {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (r : OnlineMDPRow State Action H) (s : State) :
    qLearningTrueOptimalNext E r s ∈ Set.Icc 0 (H:ℝ) := by
  have h := onlineTrueOptimalValue_range_length ((List.ofFn E).drop (r.1.val+1)) s
  have hlen : (((List.ofFn E).drop (r.1.val+1)).length : ℝ) ≤ H := by
    have hn : ((List.ofFn E).drop (r.1.val+1)).length ≤ H := by simp
    exact_mod_cast hn
  exact ⟨h.1, h.2.trans hlen⟩
end StatisticalRL.OnlineRL

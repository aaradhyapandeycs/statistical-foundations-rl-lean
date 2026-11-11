import Formalization.Online.QLearning.EpisodeTargetsIndex
import Formalization.Online.QLearning.OptimalQDefinitions

/-! True finite-horizon Bellman Q in the actual row indexing. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem qLearningTrueOptimalQ_mem_Icc {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (r : OnlineMDPRow State Action H) :
    qLearningTrueOptimalQ E r ∈ Set.Icc 0 (H:ℝ) := by
  let tail := (List.ofFn E).drop (r.1.val+1)
  have hv := onlineTrueOptimalValue_range_length tail
  have hlo := ((E r.1).transition r.2.1 r.2.2).expectation_nonneg (fun s => (hv s).1)
  have hhi := ((E r.1).transition r.2.1 r.2.2).expectation_le_const (fun s => (hv s).2)
  have hrlo := (E r.1).reward_nonneg r.2.1 r.2.2
  have hrhi := (E r.1).reward_le_one r.2.1 r.2.2
  have hlen : tail.length+1 ≤ H := by dsimp [tail]; simp only [List.length_drop,List.length_ofFn]; have := r.1.isLt; omega
  have hlenR : (tail.length:ℝ)+1 ≤ H := by exact_mod_cast hlen
  change 0 ≤ (E r.1).reward r.2.1 r.2.2 +
      ((E r.1).transition r.2.1 r.2.2).expectation (EnvironmentStage.optimalValue tail) ∧
    (E r.1).reward r.2.1 r.2.2 +
      ((E r.1).transition r.2.1 r.2.2).expectation (EnvironmentStage.optimalValue tail) ≤ (H:ℝ)
  exact ⟨by linarith,by linarith⟩
end StatisticalRL.OnlineRL

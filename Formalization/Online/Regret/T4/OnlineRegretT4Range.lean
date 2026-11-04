import Formalization.Online.Regret.T4.OnlineRegretT4ActualBridge

/-! actual-episode T4 increment and deterministic range.
No conditional centering or probability bound is asserted here. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def onlineT4EpisodeReturn
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) : ℝ :=
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  ∑ n ∈ Finset.range H,
    if hn : n < H then (E ⟨n, hn⟩).reward
      (onlineT4EpisodeState H K initial fallback history k.val n)
      (onlineT4PlayedAction H K hH initial fallback planner path k ⟨n, hn⟩)
    else 0

noncomputable def onlineT4EpisodeIncrement
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) : ℝ :=
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  onlineT4EpisodeReturn H K hH E initial fallback planner path k -
    onlineT4SelectedEpisodeValue H hH E planner history k.val (initial k)

theorem onlineT4EpisodeReturn_nonneg
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) :
    0 ≤ onlineT4EpisodeReturn H K hH E initial fallback planner path k := by
  unfold onlineT4EpisodeReturn
  apply Finset.sum_nonneg
  intro n hn
  simp only [dif_pos (Finset.mem_range.mp hn)]
  exact (E ⟨n, Finset.mem_range.mp hn⟩).reward_nonneg _ _

theorem onlineT4EpisodeReturn_le_horizon
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) :
    onlineT4EpisodeReturn H K hH E initial fallback planner path k ≤ (H : ℝ) := by
  unfold onlineT4EpisodeReturn
  calc
    _ ≤ ∑ _n ∈ Finset.range H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [dif_pos (Finset.mem_range.mp hn)]
      exact (E ⟨n, Finset.mem_range.mp hn⟩).reward_le_one _ _
    _ = (H : ℝ) := by simp

/-- The actual source episode increment is bounded by H without imposing
any assumption on the sampled history, tie rule, or transition probabilities. -/
theorem onlineT4EpisodeIncrement_abs_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) :
    |onlineT4EpisodeIncrement H K hH E initial fallback planner path k| ≤ (H : ℝ) := by
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let g := planner (history.take (k.val * H))
  have hv : onlineT4SelectedEpisodeValue H hH E planner history k.val (initial k) =
      DecisionStage.trajectoryValue (onlineFixedPolicyStages E g) (initial k) := by
    unfold onlineT4SelectedEpisodeValue
    rw [onlineT4SelectedStages_eq_fixed]
  have hvlo := onlineFixedPolicyValue_nonneg E g 0 (initial k)
  have hvhi := onlineFixedPolicyValue_le_horizon E g 0 (initial k)
  simp only [List.drop_zero] at hvlo hvhi
  have hrlo := onlineT4EpisodeReturn_nonneg H K hH E initial fallback planner path k
  have hrhi := onlineT4EpisodeReturn_le_horizon H K hH E initial fallback planner path k
  change |onlineT4EpisodeReturn H K hH E initial fallback planner path k -
    onlineT4SelectedEpisodeValue H hH E planner history k.val (initial k)| ≤ (H : ℝ)
  rw [hv, abs_le]
  constructor <;> linarith

end StatisticalRL.OnlineRL

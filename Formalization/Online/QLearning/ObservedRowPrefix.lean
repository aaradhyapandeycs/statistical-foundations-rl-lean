import Formalization.Online.QLearning.StackRows
import Formalization.Online.SourceOptimism.ObservedEmpiricalPrefix

/-! Deterministic equality of observed row prefixes and stack prefixes;
no probabilistic conditional-independence assertion. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance qLearningObservedStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance qLearningObservedActionDecidable : DecidableEq Action := Classical.decEq Action

theorem qLearning_observedPrefix_eq_stack {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (bonus : ℕ → ℝ)
    (initial : Fin K → State) (fallback : State)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (n : ℕ) (hn : n ≤ K*H) (r : OnlineMDPRow State Action H)
    (t : ℕ) (ht : t ≤ (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback
      (qLearningActualEpisodePlanner hH E bonus) data n) r).length) :
    (fun i : Fin t => (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback
      (qLearningActualEpisodePlanner hH E bonus) data n) r).getD i.val fallback) =
    onlineStackRowPrefix K t (ht.trans (qLearning_stack_rowCount_le hH E bonus initial fallback data n hn r)) r data := by
  funext i
  have hi : i.val < (onlineRowOutcomes (onlineMVPActualStackHistory hH initial fallback
      (qLearningActualEpisodePlanner hH E bonus) data n) r).length := i.isLt.trans_le ht
  have h := qLearning_stack_rowNth_eq hH E bonus initial fallback data n hn r ⟨i.val,hi⟩
  rw [List.getD_eq_get _ fallback ⟨i.val,hi⟩]
  simpa [onlineStackRowPrefix] using h
end StatisticalRL.OnlineRL

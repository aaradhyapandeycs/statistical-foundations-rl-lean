import Formalization.Online.Regret.T5.OnlineT5Decomposition
import Formalization.Online.Regret.Telescope

/-! Actual-law variance and gap proof component: OnlineT5Successor.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t5SuccState : DecidableEq State := Classical.decEq State
noncomputable local instance t5SuccAction : DecidableEq Action := Classical.decEq Action

theorem onlineT5ActualSuccessor_eq_next_state
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) (hnext : h.val + 1 < H) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    onlineT5ActualSuccessor H K hH E initial fallback path δ c₁ c₂ h k =
      onlineEpisodicCurrentState H K initial fallback (history.take (k.val * H + (h.val + 1))) := by
  dsimp only
  symm
  exact onlineSequentialEpisode_successor_state H K hH initial fallback
    (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂) path k h hnext

theorem onlineActualOptimisticContinuation_terminal
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) (hlast : h.val + 1 = H) (s : State) :
    onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k s = 0 := by
  unfold onlineActualOptimisticContinuation onlineCappedBackwardValueAt
  rw [hlast]
  rw [List.drop_eq_nil_of_le]
  · rfl
  · simp only [onlinePreEpisodePlanningStages_length, le_refl]
end StatisticalRL.OnlineRL

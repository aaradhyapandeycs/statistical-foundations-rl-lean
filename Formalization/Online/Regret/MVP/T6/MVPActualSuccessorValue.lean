import Formalization.Online.Regret.MVP.T6.MVPActualSuccessor
import Formalization.Online.Regret.MVP.T6.MVPVarianceEpisodeBudget
import Formalization.Online.Regret.T2.OnlineT2ActualAlignment

/-! Actual-law variance and gap proof component: OnlineT5ActualShift.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t6MVPActualSuccessorValue_t5ShiftStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t6MVPActualSuccessorValue_t5ShiftActionDecidable : DecidableEq Action := Classical.decEq Action

theorem mvpActualSuccessor_value_eq_episode_next
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (h : Fin H) (k : Fin K) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let stages := onlineMVPHistoryPlanningStages hH E fallback (history.take (k.val * H))
    mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
      (mvpVarianceSuccessor H K hH E initial fallback path δ c₁ c₂ h k) =
      onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ)) c₁ c₂
        (stages.drop (h.val + 1))
        (onlineEpisodicCurrentState H K initial fallback (history.take (k.val * H + (h.val + 1)))) := by
  classical
  dsimp only
  by_cases hnext : h.val + 1 < H
  · rw [mvpVarianceSuccessor_eq_next_state H K hH E initial fallback path δ c₁ c₂ h k hnext]
    rfl
  · have hlast : h.val + 1 = H := by omega
    rw [mvpVarianceContinuation_terminal H K hH E initial fallback path δ c₁ c₂ h k hlast]
    simp only [hlast]
    rw [List.drop_eq_nil_of_le (by simp [onlineMVPHistoryPlanningStages])]
    rfl
end StatisticalRL.OnlineRL

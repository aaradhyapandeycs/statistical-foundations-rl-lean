import Formalization.Online.Regret.MVP.T6.MVPActualVarianceDefinitions
import Formalization.Online.Regret.MVP.T6.MVPEmptyTableVariance

/-! K=1 has an empty pre-episode MVP table and therefore zero true-row tail variance. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvp_actualT6UCB_one_episode_zero
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin 1 → State) (fallback : State) (path : OnlineOutcomePath State (1*H))
    (δ c₁ c₂ : ℝ) :
    mvpVarianceT6UCB H 1 hH E initial fallback path δ c₁ c₂ = 0 := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  unfold mvpVarianceT6UCB
  apply Finset.sum_eq_zero
  intro h hh
  apply Finset.sum_eq_zero
  intro k hk
  have hk0 : k.val = 0 := by have := k.isLt; omega
  let stages := onlineMVPHistoryPlanningStages hH E fallback []
  have hz : ∀ stage ∈ stages, ∀ s a, (stage.observations s a).length = 0 := by
    intro stage hs s a
    simp only [stages, onlineMVPHistoryPlanningStages, List.mem_ofFn] at hs
    obtain ⟨j, rfl⟩ := hs
    simp [onlineMVPActualPlanningStage, onlineMVPRowVisitList,
      onlineMVPSourceBatchList, onlineMVPSourceBatchStart, onlineMVPSourceBatchEnd,
      onlineMVPStoredCount, onlineMVPRowCountState]
  have hv := mvp_emptyStages_tail_variance_zero (H : ℝ) (Real.log (1/δ)) c₁ c₂
    stages hz (h.val+1)
    ((E h).transition
      (onlineActualStageRowSequence H 1 hH initial fallback
        (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂) path h k.val).1
      (onlineActualStageRowSequence H 1 hH initial fallback
        (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂) path h k.val).2)
  simpa [mvpVarianceContinuation, hk0, stages] using hv
end StatisticalRL.OnlineRL

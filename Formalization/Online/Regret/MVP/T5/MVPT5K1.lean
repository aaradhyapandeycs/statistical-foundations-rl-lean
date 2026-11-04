import Formalization.Online.Regret.MVP.T5.MVPT5Decomposition
import Formalization.Online.Regret.MVP.T6.MVPEmptyTableVariance

/-! Initial-episode empirical variance and W3 endpoints. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvp_empty_history_tail_is_constant
    (H : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) (n : ℕ) :
    ∃ c : ℝ, ∀ s, onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δ)) c₁ c₂
      (onlineMVPHistoryPlanningStages hH E fallback []) n s = c := by
  classical
  let stages := onlineMVPHistoryPlanningStages hH E fallback []
  have hz : ∀ stage ∈ stages, ∀ s a, (stage.observations s a).length = 0 := by
    intro stage hs s a
    simp only [stages, onlineMVPHistoryPlanningStages, List.mem_ofFn] at hs
    obtain ⟨j, rfl⟩ := hs
    simp [onlineMVPActualPlanningStage, onlineMVPRowVisitList,
      onlineMVPSourceBatchList, onlineMVPSourceBatchStart, onlineMVPSourceBatchEnd,
      onlineMVPStoredCount, onlineMVPRowCountState]
  have hdrop : ∀ stage ∈ stages.drop n, ∀ s a, (stage.observations s a).length = 0 := by
    intro stage hs
    exact hz stage (List.mem_of_mem_drop hs)
  simpa [onlineCappedBackwardValueAt, stages] using
    mvp_emptyStages_value_constant (H : ℝ) (Real.log (1/δ)) c₁ c₂ (stages.drop n) hdrop

theorem mvp_actualT5_W3_one_episode_zero
    (H : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin 1 → State) (fallback : State) (path : OnlineOutcomePath State (1*H))
    (δ c₁ c₂ : ℝ) :
    mvpActualT5 H 1 hH E initial fallback path δ c₁ c₂ = 0 ∧
    mvpActualW3 H 1 hH E initial fallback path δ c₁ c₂ = 0 := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  constructor
  · unfold mvpActualT5
    apply Finset.sum_eq_zero
    intro h hh
    apply Finset.sum_eq_zero
    intro k hk
    have hk0 : k.val = 0 := by have := k.isLt; omega
    obtain ⟨c,hc⟩ := mvp_empty_history_tail_is_constant H hH E fallback δ c₁ c₂ (h.val+1)
    have heq : mvpVarianceContinuation H 1 hH E initial fallback path δ c₁ c₂ h k = fun _ => c := by
      funext s
      simpa [mvpVarianceContinuation, hk0] using hc s
    simp [heq, FiniteDistribution.variance_const]
  · unfold mvpActualW3
    apply Finset.sum_eq_zero
    intro h hh
    apply Finset.sum_eq_zero
    intro k hk
    have hk0 : k.val = 0 := by have := k.isLt; omega
    obtain ⟨c,hc⟩ := mvp_empty_history_tail_is_constant H hH E fallback δ c₁ c₂ (h.val+1)
    have heq : mvpVarianceContinuation H 1 hH E initial fallback path δ c₁ c₂ h k = fun _ => c := by
      funext s
      simpa [mvpVarianceContinuation, hk0] using hc s
    simp [heq, FiniteDistribution.expectation_const]
end StatisticalRL.OnlineRL

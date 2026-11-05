import Formalization.Online.Regret.MVP.Decoupling.MVPDecouplingFirstInequality
import Formalization.Online.Regret.MVP.T5.MVPT5K1

/-! Direct one-episode endpoint for the actual decoupling event, for every
positive horizon. The H transition outcomes remain in the experiment. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualW4_one_episode_zero
    (H : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin 1 → State) (fallback : State) (path : OnlineOutcomePath State (1*H))
    (δplan c₁ c₂ : ℝ) :
    mvpVarianceW4 H 1 hH E initial fallback path δplan c₁ c₂ = 0 := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  unfold mvpVarianceW4
  apply Finset.sum_eq_zero
  intro h hh
  apply Finset.sum_eq_zero
  intro k hk
  have hk0 : k.val = 0 := by have := k.isLt; omega
  obtain ⟨c,hc⟩ := mvp_empty_history_tail_is_constant H hH E fallback δplan c₁ c₂ (h.val+1)
  have heq : mvpVarianceContinuation H 1 hH E initial fallback path δplan c₁ c₂ h k =
      fun _ => c := by
    funext s
    simpa [mvpVarianceContinuation,hk0] using hc s
  simp [heq, FiniteDistribution.expectation_const]

theorem mvpActualDecouplingEvent_one_episode_eq_univ
    (H : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δplan c₁ c₂ : ℝ) :
    mvpActualDecouplingEvent H 1 hH E fallback δplan c₁ c₂ 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro sample
  dsimp only [mvpActualDecouplingEvent, Set.mem_setOf_eq]
  refine ⟨mvpActualT1_le_W4 H 1 hH E sample.1 fallback sample.2 δplan c₁ c₂, ?_, ?_⟩
  · rw [mvpActualW4_one_episode_zero]
    simp
  · rw [(mvp_actualT5_W3_one_episode_zero H hH E sample.1 fallback sample.2 δplan c₁ c₂).2]
    simp

end StatisticalRL.OnlineRL

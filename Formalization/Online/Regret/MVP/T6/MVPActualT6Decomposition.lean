import Formalization.Online.Regret.MVP.T6.MVPActualEpisodeRemainder

/-! Deterministic MVP T6 bound on the actual path, without an optimism event. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def mvpVarianceRemainder (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
    (U (mvpVarianceSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2 -
      (((E h).transition sa.1 sa.2).expectation U)^2

theorem mvp_actualT6_eq_T8_add_remainder (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) :
    mvpVarianceT6UCB H K hH E initial fallback path δ c₁ c₂ =
      mvpVarianceT8 H K hH E initial fallback path δ c₁ c₂ +
      mvpVarianceRemainder H K hH E initial fallback path δ c₁ c₂ := by
  classical
  unfold mvpVarianceT6UCB mvpVarianceT8 mvpVarianceRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  unfold FiniteDistribution.variance
  ring

theorem mvp_actualT6_le_T8_T2_W4 (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ)
    (hL : 0 ≤ Real.log (1/δ)) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    mvpVarianceT6UCB H K hH E initial fallback path δ c₁ c₂ ≤
      mvpVarianceT8 H K hH E initial fallback path δ c₁ c₂ +
      2*(H : ℝ)*mvpVarianceT2 H K hH E initial fallback path δ c₁ c₂ +
      2*(K : ℝ)*(H : ℝ)^2 +
      2*(H : ℝ)*mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂ := by
  classical
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    mvp_actual_episode_remainder_bound H K hH E initial fallback path δ c₁ c₂ hL hc₁ hc₂ k)
  have hr : mvpVarianceRemainder H K hH E initial fallback path δ c₁ c₂ ≤
      2*(H : ℝ)*mvpVarianceT2 H K hH E initial fallback path δ c₁ c₂ +
      2*(K : ℝ)*(H : ℝ)^2 +
      2*(H : ℝ)*mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂ := by
    unfold mvpVarianceRemainder mvpVarianceT2 mvpVarianceW4
    simp_rw [mul_add] at hs
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    nth_rw 1 [Finset.sum_comm] at hs
    nth_rw 2 [Finset.sum_comm] at hs
    nth_rw 3 [Finset.sum_comm] at hs
    nlinarith
  rw [mvp_actualT6_eq_T8_add_remainder]
  linarith
end StatisticalRL.OnlineRL

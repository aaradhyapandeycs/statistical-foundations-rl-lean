import Formalization.Online.Regret.MVP.T5.MVPT5Decomposition
import Formalization.Online.Regret.MVP.T5.MVPT5ActualEpisode

/-! Actual-path T5 bound before the T8 tail estimate. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualT5_le_W3_T8_T2
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    mvpActualT5 H K hH E initial fallback path δ c₁ c₂ ≤
      mvpActualW3 H K hH E initial fallback path δ c₁ c₂ +
      mvpVarianceT8 H K hH E initial fallback path δ c₁ c₂ +
      2*(H : ℝ)*mvpVarianceT2 H K hH E initial fallback path δ c₁ c₂ + 2*(K : ℝ)*(H : ℝ)^2 := by
  classical
  have hL : 0 ≤ Real.log (1/δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    mvp_actual_episode_empirical_remainder_bound H K hH E initial fallback path δ c₁ c₂ hL hc₁ hc₂ k)
  have hrem : mvpActualT5Remainder H K hH E initial fallback path δ c₁ c₂ ≤
      2*(H : ℝ)*mvpVarianceT2 H K hH E initial fallback path δ c₁ c₂ + 2*(K : ℝ)*(H : ℝ)^2 := by
    unfold mvpActualT5Remainder mvpVarianceT2
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ k : Fin K, 2*(H : ℝ)*((∑ h : Fin H,
        let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
        let history := mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂
        let prehist := history.take (k.val*H)
        let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
        letI : Nonempty State := (E h).state_nonempty
        let stage := onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback prehist)
          (onlineMVPHistoryNextAt fallback prehist) prehist.length h
        let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
        onlineRegretAnalysisCharge (H : ℝ) (Real.log (1/δ)) c₁ c₂ stage U sa.1 sa.2) + H) := hsum
      _ = _ := by simp_rw [mul_add]; rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; rw [Finset.sum_comm]; ring
  rw [mvpActualT5_eq_W3_add_T8_add_remainder H K hH E initial fallback path δ c₁ c₂]
  linarith
end StatisticalRL.OnlineRL

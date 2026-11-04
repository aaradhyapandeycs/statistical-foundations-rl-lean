import Formalization.Online.Regret.MVP.MVPT5Definitions
import Formalization.Online.Regret.MVP.T2.MVPT2ActualSource
import Formalization.Online.Regret.MVP.T6.MVPActualVarianceDefinitions

/-! Same-path decomposition of empirical T5 for the actual retained
MVP table. This does not assert a martingale or concentration bound. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def mvpActualT5Remainder (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) : ℝ :=
  ∑ h : Fin H, ∑ k : Fin K,
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let hist := (mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂).take (k.val*H)
    letI : Nonempty State := (E h).state_nonempty
    let stage := onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
      (onlineMVPHistoryNextAt fallback hist) hist.length h
    let U := mvpVarianceContinuation H K hH E initial fallback path δ c₁ c₂ h k
    (U (mvpVarianceSuccessor H K hH E initial fallback path δ c₁ c₂ h k))^2 -
      ((onlineObservedPlanningRow stage sa.1 sa.2).expectation U)^2

theorem mvpActualT5_eq_W3_add_T8_add_remainder
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) :
    mvpActualT5 H K hH E initial fallback path δ c₁ c₂ =
      mvpActualW3 H K hH E initial fallback path δ c₁ c₂ +
      mvpVarianceT8 H K hH E initial fallback path δ c₁ c₂ +
      mvpActualT5Remainder H K hH E initial fallback path δ c₁ c₂ := by
  classical
  unfold mvpActualT5 mvpActualW3 mvpVarianceT8 mvpActualT5Remainder
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  simp only [FiniteDistribution.variance]
  ring
end StatisticalRL.OnlineRL

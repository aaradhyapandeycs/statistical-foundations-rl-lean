import Formalization.Online.Regret.MVP.T6.MVPActualVarianceDefinitions
import Formalization.Online.Regret.T5.OnlineT5Scalar

/-! Nonnegativity on the same actual MVP path; no concentration premise. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpVarianceT6UCB_nonneg (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) :
    0 ≤ mvpVarianceT6UCB H K hH E initial fallback path δ c₁ c₂ := by
  unfold mvpVarianceT6UCB
  apply Finset.sum_nonneg
  intro h _
  apply Finset.sum_nonneg
  intro k _
  exact FiniteDistribution.variance_nonneg _ _

theorem mvpVarianceT2_nonneg (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ)
    (hL : 0 ≤ Real.log (1/δ)) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    0 ≤ mvpVarianceT2 H K hH E initial fallback path δ c₁ c₂ := by
  unfold mvpVarianceT2
  apply Finset.sum_nonneg
  intro h _
  apply Finset.sum_nonneg
  intro k _
  apply onlineRegretAnalysisCharge_nonneg_for_T5
  · positivity
  · exact hL
  · exact hc₁
  · exact hc₂

theorem mvpVarianceW4_nonneg (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δ c₁ c₂ : ℝ) :
    0 ≤ mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂ := by
  unfold mvpVarianceW4
  apply Finset.sum_nonneg
  intro h _
  apply Finset.sum_nonneg
  intro k _
  exact le_max_right _ _
end StatisticalRL.OnlineRL

import Formalization.Online.Regret.MVP.T6.MVPActualK1Variance
import Formalization.Online.Regret.MVP.T6.MVPActualVarianceNonnegative
import Formalization.Online.Regret.W1.W1Definitions

/-! K=1: the actual retained table is empty, so T6 vanishes. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvp_actualT6_one_episode_bound (H : ℕ) (hH : 0<H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin 1 → State)
    (fallback : State) (path : OnlineOutcomePath State (1*H)) (δ c₁ c₂ : ℝ)
    (hL : 0 ≤ Real.log (1/δ)) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    mvpVarianceT6UCB H 1 hH E initial fallback path δ c₁ c₂ ≤
      4*(H : ℝ)*mvpVarianceT2 H 1 hH E initial fallback path δ c₁ c₂ +
      4*(H : ℝ)*mvpVarianceW4 H 1 hH E initial fallback path δ c₁ c₂ +
      1*(H : ℝ)^2*onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H 1 δ := by
  rw [mvp_actualT6UCB_one_episode_zero]
  have ht := mvpVarianceT2_nonneg H 1 hH E initial fallback path δ c₁ c₂ hL hc₁ hc₂
  have hw := mvpVarianceW4_nonneg H 1 hH E initial fallback path δ c₁ c₂
  simp [onlineW1SourceIota]
  positivity
end StatisticalRL.OnlineRL

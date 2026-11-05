import Formalization.Online.Regret.MVP.MVPDecouplingDefinitions

/-! Deterministic signed-error versus positive-error comparison. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualT1_le_W4 (H K : ℕ) (hH : 0<H)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (path : OnlineOutcomePath State (K*H)) (δplan c₁ c₂ : ℝ) :
    mvpActualT1 H K hH E initial fallback path δplan c₁ c₂ ≤
      mvpVarianceW4 H K hH E initial fallback path δplan c₁ c₂ := by
  unfold mvpActualT1 mvpVarianceW4
  apply Finset.sum_le_sum
  intro h _
  apply Finset.sum_le_sum
  intro k _
  dsimp only
  exact le_max_left _ _

end StatisticalRL.OnlineRL

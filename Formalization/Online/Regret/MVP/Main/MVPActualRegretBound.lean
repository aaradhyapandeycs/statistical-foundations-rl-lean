import Formalization.Online.Regret.MVP.Main.MVPRegretAlignment

/-! actual MVP regret decomposition under the actual optimism event. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualRegret_le_W4_T2_T3_T4_of_optimism
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ : ℝ) (hδ : 0<δ) (hδsmall : δ≤1/100) (hc₁ : 4≤c₁) (hc₂ : c₁^2≤c₂)
    (hopt : mvpHistoryAllStageOptimism (K := K) hH E fallback δ c₁ c₂
      (mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂)) :
    (∑ k : Fin K, mvpActualEpisodeRegret H K hH E initial fallback path k δ c₁ c₂) ≤
      mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂ +
      mvpVarianceT2 H K hH E initial fallback path δ c₁ c₂ +
      mvpActualT3 H K hH E initial fallback path δ c₁ c₂ +
      mvpActualT4 H K hH E initial fallback path (Real.log (1/δ)) c₁ c₂ := by
  have hd := mvpActualRegret_le_decomposition_of_optimism H K hH E initial fallback path δ c₁ c₂ hδ hδsmall hc₁ hc₂ hopt
  have ha := mvpRegret_components_align H K hH E initial fallback path δ c₁ c₂
  rw [ha.2.1, ha.2.2.1, ha.2.2.2] at hd
  linarith [ha.1]
end StatisticalRL.OnlineRL

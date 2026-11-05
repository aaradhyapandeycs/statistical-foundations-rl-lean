import Formalization.Online.Regret.MVP.Main.MVPActualRegretBound
import Formalization.Online.Regret.MVP.Main.MVPVarianceClosure
import Formalization.Online.Regret.MVP.Main.MVPRegretRateScalar

/-! Conditional actual-path large-regime consumer. The component bounds are
intermediate premises; their simultaneous actual-law production remains separate. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualRegret_large_of_components
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ c₁ c₂ d I T5 T6 W3 : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1/100) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hopt : mvpHistoryAllStageOptimism (K := K) hH E fallback δ c₁ c₂
      (mvpVarianceHistory H K hH E initial fallback path δ c₁ c₂))
    (hd : 1 ≤ d) (hI : 1 ≤ I) (hK : d*I ≤ K)
    (h5n : 0 ≤ T5) (h6n : 0 ≤ T6)
    (h2 : mvpVarianceT2 H K hH E initial fallback path δ c₁ c₂ ≤
      (1/2 : ℝ)*Real.sqrt (d*T5*I)+(1/2 : ℝ)*d*H*I)
    (h4 : mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂ ≤
      Real.sqrt (d*T6*I)+d*H*I)
    (h3 : W3 ≤ Real.sqrt (d*(H : ℝ)^2*T6*I)+d*(H : ℝ)^2*I)
    (h5 : T5 ≤ W3+2*H*mvpVarianceT2 H K hH E initial fallback path δ c₁ c₂+
      Real.sqrt ((H : ℝ)^2*T6*I)+K*(H : ℝ)^2*I)
    (h6 : T6 ≤ 4*H*mvpVarianceT2 H K hH E initial fallback path δ c₁ c₂+
      4*H*mvpVarianceW4 H K hH E initial fallback path δ c₁ c₂+K*(H : ℝ)^2*I)
    (ht3 : mvpActualT3 H K hH E initial fallback path δ c₁ c₂ ≤ Real.sqrt (T6*I)+H*I)
    (ht4 : mvpActualT4 H K hH E initial fallback path (Real.log (1/δ)) c₁ c₂ ≤
      Real.sqrt (K*(H : ℝ)^2*I)) :
    (∑ k : Fin K, mvpActualEpisodeRegret H K hH E initial fallback path k δ c₁ c₂) ≤
      100*Real.sqrt (d*K*(H : ℝ)^2)*I := by
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hs := mvp_main_T5_T6_closure d H K I _ T5 T6 W3 _ hd hHreal hI hK h5n h6n h2 h4 h3 h5 h6
  have hr := mvpActualRegret_le_W4_T2_T3_T4_of_optimism H K hH E initial fallback path δ c₁ c₂ hδ hδsmall hc₁ hc₂ hopt
  apply mvp_main_regret_rate_large d H K I _ T5 T6 _ _ hd hHreal hI hK h5n h6n hs h2 h4
  linarith
end StatisticalRL.OnlineRL

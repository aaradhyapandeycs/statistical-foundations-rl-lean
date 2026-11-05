import Formalization.Online.Regret.MVP.Main.MVPActualRegret
import Formalization.Online.Regret.MVP.Main.MVPSmallRegime
import Formalization.Online.Regret.W1.OnlineUCBVISourceIota

/-! Deterministic actual-path small-regime rate, including K=1. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem mvpActualRegret_small_regime
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δp : ℝ)
    (hsmall : (K : ℝ) ≤ (Fintype.card State : ℝ)*Fintype.card Action*H*
      max 1 (onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp)) :
    (∑ k : Fin K, mvpActualEpisodeRegret H K hH E initial fallback path k δp 4 16) ≤
      100*max 1 (onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp)*
      min ((K : ℝ)*H) (Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*K*(H : ℝ)^2)) := by
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  have hs : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos (α := State)
  have ha : (1 : ℝ) ≤ Fintype.card Action := by exact_mod_cast Fintype.card_pos (α := Action)
  have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hd : (1 : ℝ) ≤ (Fintype.card State : ℝ)*Fintype.card Action*H := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hs ha) hh
  exact mvp_main_small_regime_rate _ _ _ _ _ hd hh (by positivity) (le_max_left _ _) hsmall
    (mvpActualRegret_sum_le_KH H K hH E initial fallback path δp 4 16)
end StatisticalRL.OnlineRL

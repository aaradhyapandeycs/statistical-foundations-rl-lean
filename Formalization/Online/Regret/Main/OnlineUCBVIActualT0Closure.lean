import Formalization.Online.Regret.Main.OnlineUCBVIT0Closure
import Formalization.Online.Regret.W1.OnlineUCBVISourceIota
import Formalization.Online.Regret.T0.OnlineT0SourceDefinition
import Formalization.Online.Regret.T2.OnlineT2SourceBound
import Formalization.Probability.OnlineT56ScalarAlgebra

/-! Actual-source T0 scalar consumer at c₁=4,c₂=16. The simplified T5,
policy-variance and difference-variance bounds are explicit event premises. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineUCBVI_actual_T0_closure_of_component_bounds
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hV : onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ 4 16 ≤ 2 * (K : ℝ) * H^2)
    (h5 : onlineActualT5 H K hH E sample.1 fallback sample.2 δ 4 16 ≤
      6 * (K : ℝ) * H^2 + (1 / 2 : ℝ) * Real.sqrt ((Fintype.card State : ℝ)^2 * Fintype.card Action * H^3 *
        onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ 4 16 *
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ) +
      4 * (Fintype.card State : ℝ)^2 * Fintype.card Action * H^3 *
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ)
    (hD : onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ 4 16 ≤
      2 * (H : ℝ)^2 * onlineActualT0SourceUpper H K hH E fallback sample δ 4 16 +
        18 * (H : ℝ)^2 * Real.log (1 / δ)) :
    onlineActualT0SourceUpper H K hH E fallback sample δ 4 16 ≤
      20 * Real.sqrt ((Fintype.card State : ℝ) * Fintype.card Action * H^3 * K) *
          onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ +
      15 * (Fintype.card State : ℝ)^2 * Fintype.card Action * H^3 *
          onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  have hs : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos (α := State)
  have ha : (1 : ℝ) ≤ Fintype.card Action := by exact_mod_cast Fintype.card_pos (α := Action)
  have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hl : 1 ≤ Real.log (1 / δ) := onlineSmallConfidence_log_ge_one δ hδ hδsmall
  have hi := onlineT56_source_iota_large (Fintype.card State) (Fintype.card Action) H K δ
    Fintype.card_pos Fintype.card_pos hH hK hδ hδsmall
  have hi1 : 1 ≤ onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ := by nlinarith
  have hli : Real.log (1 / δ) ≤ onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ := by nlinarith
  have hDn : 0 ≤ onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ 4 16 := by
    unfold onlineActualT6Difference
    apply Finset.sum_nonneg
    intro h hh'
    apply Finset.sum_nonneg
    intro k hk'
    exact FiniteDistribution.expectation_nonneg _ (fun _ => sq_nonneg _)
  have hthreshold := onlineUCBVI_iota_meets_T2_constants (Fintype.card State) (Fintype.card Action) H K δ
    Fintype.card_pos Fintype.card_pos hH hK hδ hδsmall
  have h2 := onlineActualT2_le_sourceBound H K hH hK E sample.1 fallback sample.2 δ 4 16
    (onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ)
    hδ hδsmall (by norm_num) (by norm_num) hthreshold
  exact onlineUCBVI_T0_source_closure (Fintype.card State) (Fintype.card Action) H K
    (onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ) (Real.log (1 / δ))
    (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ 4 16)
    (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ 4 16)
    (onlineActualT5 H K hH E sample.1 fallback sample.2 δ 4 16)
    (onlineActualT2 H K hH E sample.1 fallback sample.2 δ 4 16)
    (onlineActualT0SourceUpper H K hH E fallback sample δ 4 16)
    hs ha hh hk hi1 (by linarith) hli hDn hV h5 h2 (le_refl _) hD
end StatisticalRL.OnlineRL

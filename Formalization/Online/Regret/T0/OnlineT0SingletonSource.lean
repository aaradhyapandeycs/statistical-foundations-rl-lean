import Formalization.Online.Regret.T0.OnlineT0UniformConditional

/-! Same-experiment suffix proof component: OnlineT0SingletonSource.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

theorem onlineSingleton_actualStageGap_uniform_le_sourceT0 [Subsingleton State]
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    ∀ j : Fin H, (∑ k : Fin K,
      onlineActualStagePolicyGap H K hH E sample.1 fallback sample.2 δ c₁ c₂ j k) ≤
      onlineActualT0SourceUpper H K hH E fallback sample δ c₁ c₂ := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  have hL : 0 ≤ Real.log (1 / δ) := by
    exact (onlineSmallConfidence_log_ge_one δ hδ hδsmall).trans' (by norm_num)
  have hI : 0 ≤ onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ := by
    have hi := onlineT56_source_iota_large (Fintype.card State) (Fintype.card Action) H K δ
      Fintype.card_pos Fintype.card_pos hH hK hδ hδsmall
    nlinarith
  intro j
  have hg := onlineSingleton_actual_stageGap_le_T2 H K hH E sample.1 fallback sample.2 δ c₁ c₂
    hδ hδsmall hc₁ hc₂ j
  have hT0 : onlineActualT2 H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤
      onlineActualT0SourceUpper H K hH E fallback sample δ c₁ c₂ := by
    unfold onlineActualT0SourceUpper
    dsimp only
    have hlin : 0 ≤ (1 / 4 : ℝ) * (Fintype.card State : ℝ)^2 *
        (Fintype.card Action : ℝ) * (H : ℝ)^2 *
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ := by positivity
    have hnoise : 0 ≤ 7 * Real.sqrt ((K : ℝ) * (H : ℝ)^2) * Real.log (1 / δ) := by positivity
    have hrV := Real.sqrt_nonneg ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H *
      onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂ *
      onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ)
    have hrD := Real.sqrt_nonneg ((Fintype.card State : ℝ)^2 * (Fintype.card Action : ℝ) * H *
      onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂ *
      onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ)
    linarith
  exact hg.trans hT0
end StatisticalRL.OnlineRL

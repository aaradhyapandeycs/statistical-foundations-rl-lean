import Formalization.Online.Regret.W1.W1Definitions
import Formalization.Online.Regret.T2.OnlineT2ActualDefinitions

/-! Same-experiment suffix proof component: OnlineT0SourceDefinition.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

noncomputable def onlineActualT0SourceUpper
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (sample : (Fin K → State) × OnlineOutcomePath State (K * H))
    (δ' c₁ c₂ : ℝ) : ℝ :=
  let S : ℝ := Fintype.card State
  let A : ℝ := Fintype.card Action
  let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ'
  let L := Real.log (1 / δ')
  (3 / 8 : ℝ) * Real.sqrt (S * A * H *
    onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * I) +
  (3 / 8 : ℝ) * Real.sqrt (S^2 * A * H *
    onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * I) +
  (1 / 4 : ℝ) * S^2 * A * H^2 * I +
  7 * Real.sqrt ((K : ℝ) * H^2) * L +
  onlineActualT2 H K hH E sample.1 fallback sample.2 δ' c₁ c₂

end StatisticalRL.OnlineRL

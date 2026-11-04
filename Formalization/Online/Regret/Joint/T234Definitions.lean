import Formalization.Online.Regret.T2.OnlineT2ActualDefinitions
import Formalization.Online.Regret.T3.T3Definitions

/-! Actual same-experiment joint T2/T3/T4 event. The iota parameter must
satisfy the source lower bound in the applying concentration theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]

noncomputable def onlineActualT234SourceEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ' c₁ c₂ I : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  {sample |
    onlineActualT2 H K hH E sample.1 fallback sample.2 δ' c₁ c₂ ≤
      (1 / 2 : ℝ) * Real.sqrt ((Fintype.card State : ℝ) * Fintype.card Action * H *
        onlineActualT5 H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * I) +
      (1 / 2 : ℝ) * (Fintype.card State : ℝ) * Fintype.card Action * H^2 * I ∧
    onlineActualT3SourceBoundEvent H K hH E fallback δ' c₁ c₂ sample ∧
    |∑ k : Fin K,
      (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.2.2| ≤
      Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * Real.log (1 / δ'))}

end StatisticalRL.OnlineRL

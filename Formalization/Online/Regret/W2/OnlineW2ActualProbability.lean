import Formalization.Online.Regret.W2.OnlineW2ActualCumulative

/-! OnlineW1PolicyProbability: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w2PolicyProbabilityStateMeasurable : MeasurableSpace State := ⊤
local instance w2PolicyProbabilityAtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

noncomputable def onlineActualW2PolicyBudgetEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
  {sample |
    let S := (Fintype.card State : ℝ)
    let A := S * (Fintype.card Action : ℝ) * H
    let L := Real.log (1 / δ)
    let R := A * (1 + Real.log (K + 1 : ℝ))
    (∑ k : Fin K, onlineActualEpisodeW2 H K hH E sample.1 fallback sample.2 k δ c₁ c₂) ≤
      H * (3 * A) +
      Real.sqrt (2 * (S * L) * onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂) * Real.sqrt R +
      S * H * L * R}

end StatisticalRL.OnlineRL

import Formalization.Online.Regret.W3.OnlineW3ActualCoarse

/-! OnlineW1PolicyProbability: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w3PolicyProbabilityStateMeasurable : MeasurableSpace State := ⊤
local instance w3PolicyProbabilityAtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

noncomputable def onlineActualW3CoarseBudgetEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
  {sample |
    let S := (Fintype.card State : ℝ)
    let A := S * (Fintype.card Action : ℝ) * H
    let L₀ := Real.log (1 / (2 * δ))
    let L := Real.log (1 / δ)
    let R := A * (1 + Real.log (K + 1 : ℝ))
    let p := onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂
    let d := onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂
    (∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E sample.1 fallback sample.2 δ c₁ c₂ h k) ≤
      6 * H^2 * A + Real.sqrt (2 * L₀ * (4 * H^2 * (2 * p + 2 * d))) * Real.sqrt R +
      Real.sqrt (2 * (S * L) * (4 * H^2 * d)) * Real.sqrt R +
      (2 * H^2 * L₀ / 3 + S * H^2 * L) * R}

end StatisticalRL.OnlineRL

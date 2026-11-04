import Formalization.Online.Regret.W12.OnlineW12FullRadiusIota
import Formalization.Online.Regret.W12.OnlineW12SharedEvent

/-! Same-experiment suffix proof component: OnlineW12SuffixIota.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w12IotaState : MeasurableSpace State := ⊤
local instance w12IotaAtom (K n : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

noncomputable def onlineActualW12SuffixIotaEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) : Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
  {sample |
    let S := (Fintype.card State : ℝ)
    let A := (Fintype.card Action : ℝ)
    let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ
    let p := onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂
    let d := onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂
    ∀ h0 : Fin H,
      |∑ i ∈ onlineW12SuffixIndices H K h0, onlineActualW1Point H K hH E sample.1 fallback sample.2 δ c₁ c₂ i.1 i.2| ≤
        (1 / 8 : ℝ) * Real.sqrt (S * A * H * p * I) +
        (1 / 8 : ℝ) * Real.sqrt (S * A * H * d * I) + (1 / 8 : ℝ) * S * A * H^2 * I ∧
      |∑ i ∈ onlineW12SuffixIndices H K h0, onlineActualW2Point H K hH E sample.1 fallback sample.2 δ c₁ c₂ i.1 i.2| ≤
        (1 / 8 : ℝ) * Real.sqrt (S^2 * A * H * d * I) + (1 / 8 : ℝ) * S^2 * A * H^2 * I}

theorem onlineW12SharedHistory_implies_suffixIota
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    onlineActualW12SharedHistoryEvent H K hH E fallback δ c₁ c₂ ⊆
      onlineActualW12SuffixIotaEvent H K hH E fallback δ c₁ c₂ := by
  intro sample hs
  change onlineObservedTrueW1Certificates H K E δ _ ∧
    onlineObservedW2CoordinateCertificates H K E δ _ ∧
    onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂ _ at hs
  have hb := onlineActualW12_all_suffix_le_full_radii H K hH E sample.1 fallback sample.2 δ c₁ c₂
    hδ (by linarith) hc₁ hc₂ hs.1 hs.2.1 hs.2.2
  have hi := onlineActualW12_fullRadii_le_iota H K hH hK E sample.1 fallback sample.2 δ c₁ c₂
    hδ hδsmall hc₁ hc₂ hs.2.2
  intro h0
  exact ⟨(hb h0).1.trans hi.1, (hb h0).2.trans hi.2⟩

theorem onlineSequential_actualW12SuffixIota_strict
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    1 - (4 * (Fintype.card State : ℝ) + 6) * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualW12SuffixIotaEvent H K hH E fallback δ c₁ c₂) := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)
  have hp := onlineSequential_actualW12_shared_strict H K hH (by omega) E ρ fallback δ c₁ c₂ hδ hδsmall hc₁ hc₂
  have hsub := onlineW12SharedHistory_implies_suffixIota H K hH hK E fallback δ c₁ c₂ hδ hδsmall
    (by linarith) (by nlinarith [sq_nonneg c₁])
  exact hp.trans_le (measureReal_mono hsub (measure_ne_top ν.rowMeasure _))
end StatisticalRL.OnlineRL

import Formalization.Online.Regret.MVP.T6.MVPActualT6Decomposition
import Formalization.Online.Regret.MVP.T6.MVPActualT8SourceConfidence
import Formalization.Online.Regret.MVP.T6.MVPVarianceIota
import Formalization.Online.Regret.MVP.T6.MVPVarianceScalar
import Formalization.Online.Regret.MVP.T6.MVPVarianceFailureBudget
import Formalization.Online.Regret.MVP.T6.MVPActualVarianceNonnegative

/-! The actual-law K≥2 variance event consumes the proved T8 tail. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance t6MVPActualT6LargeConfidence_mvpT6LargeState : MeasurableSpace State := ⊤
local instance t6MVPActualT6LargeConfidence_mvpT6LargeSample (H K : ℕ) : MeasurableSpace
  ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := ⊤

def mvpT6SourceEvent (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) : Set ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) :=
  {sample | mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤
    4*(H : ℝ)*mvpVarianceT2 H K hH E sample.1 fallback sample.2 δ c₁ c₂ +
    4*(H : ℝ)*mvpVarianceW4 H K hH E sample.1 fallback sample.2 δ c₁ c₂ +
    K*(H : ℝ)^2*onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ}

theorem mvpActualT6_large_confidence (H K : ℕ) (hH : 0<H) (hK : 2≤K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ) (hδ : 0<δ) (hδsmall : δ≤1/100)
    (hc₁ : 0≤c₁) (hc₂ : 0≤c₂) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
    1-4*(Fintype.card State : ℝ)*Fintype.card Action*H*K*δ ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        (mvpT6SourceEvent H K hH E fallback δ c₁ c₂) := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  have hS : 0<Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have hA : 0<Fintype.card Action := Fintype.card_pos_iff.mpr inferInstance
  have hN : 2 ≤ K*H := by nlinarith
  have hL : 0 ≤ Real.log (1/δ) := by
    have := onlineSmallConfidence_log_ge_one δ hδ hδsmall
    linarith
  have hbudget := mvp_t6_iota_budget (Fintype.card State) (Fintype.card Action) H K δ
    hS hA hH hK hδ hδsmall
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let good : Set ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := {sample |
    |mvpVarianceT8 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤
      Real.sqrt (32*(H : ℝ)^2*mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂*Real.log (1/δ)) +
        5*(H : ℝ)^2*Real.log (1/δ)}
  have hsub : good ⊆ mvpT6SourceEvent H K hH E fallback δ c₁ c₂ := by
    intro sample hs
    change |mvpVarianceT8 H K hH E sample.1 fallback sample.2 δ c₁ c₂| ≤ _ at hs
    change mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤ _
    have hv := mvpVarianceT6UCB_nonneg H K hH E sample.1 fallback sample.2 δ c₁ c₂
    have hdec := mvp_actualT6_le_T8_T2_W4 H K hH E sample.1 fallback sample.2 δ c₁ c₂ hL hc₁ hc₂
    exact mvp_t6_ucb_scalar_closure H K (onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ)
      (Real.log (1/δ)) _ _ _ _ (by positivity) hv hL hdec ((le_abs_self _).trans hs) hbudget
  have hprob := mvpActualT8_source_confidence H K hH hN E ρ fallback δ c₁ c₂ hδ hδsmall hc₁ hc₂
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have hf := mvp_t6_failure_budget (Fintype.card State) (Fintype.card Action) H K δ hS hA (le_of_lt hδ)
  change 1-4*(Fintype.card State : ℝ)*Fintype.card Action*H*K*δ ≤ μ.real _
  change 1-2*(Nat.log2 (K*H) : ℝ)*δ ≤ μ.real good at hprob
  linarith
end StatisticalRL.OnlineRL

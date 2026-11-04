import Formalization.Online.Regret.MVP.Optimism.MVPActualStackOptimism
import Formalization.Online.Regret.MVP.Optimism.MVPExpandedStackLaw

/-! The simultaneous fixed-batch event transfers through the independent
reset product to the actual retained-batch stack optimism event. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action] [Nonempty State]
local instance mvpOptProbabilityStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance mvpOptProbabilityStateEq : DecidableEq State := Classical.decEq State
noncomputable local instance mvpOptProbabilityActionEq : DecidableEq Action := Classical.decEq Action

def mvpActualStackOptimismEvent {H K : ℕ} (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (fallback : State) (δ c₁ c₂ : ℝ) :
    Set ((Fin K → State) × (OnlineMDPRow State Action H × Fin K → State)) :=
  {sample | ∀ k : Fin K, ∀ h : Fin H,
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
    let stages := onlineMVPPlanningStages E
      (onlineMVPActualStackRowAt hH sample.1 fallback planner sample.2)
      (onlineMVPActualStackNextAt hH sample.1 fallback planner sample.2) (k.val*H)
    (∀ s, EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s ≤
      onlineCappedBackwardValueAt (H : ℝ) (Real.log (1/δ)) c₁ c₂ stages h.val s) ∧
    (∀ s a, EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a ≤
      onlineCappedBackwardQAt (H : ℝ) (Real.log (1/δ)) c₁ c₂ stages h.val s a)}

theorem mvp_actualStackOptimism_probability {H K : ℕ}
    (hH : 0 < H) (hK : 0 < K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1/100) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    1-2*(Fintype.card (Fin H × State × Action) : ℝ)*K*δ <
      (onlineMDPInitialStackLaw E ρ K).real (mvpActualStackOptimismEvent hH E fallback δ c₁ c₂) := by
  classical
  let good : Set (Samples State Action H K) := {data | ∀ r n, 3 ≤ n → n < K →
    data ∈ mvpBatchBonusGood E (onlineTrueSuffixRowFamily E) K δ c₁ c₂ r n}
  have hgood := mvp_allBatchBonusGood_probability E hH K hK (onlineTrueSuffixRowFamily E)
    δ c₁ c₂ hδ (by linarith : δ ≤ 2/5) hc₁ hc₂ (onlineTrueSuffixRowFamily_range H E)
  let μ := onlineMDPInitialStackLaw E ρ K
  letI : IsProbabilityMeasure μ := by dsimp [μ, onlineMDPInitialStackLaw, onlineMDPStackLaw]; infer_instance
  have hprod : μ.real (Set.univ ×ˢ good) = (samplingLaw E K).real good := by
    dsimp [μ, onlineMDPInitialStackLaw]
    rw [measureReal_def, Measure.prod_prod, measure_univ, one_mul]
    rfl
  have hsub : (Set.univ ×ˢ good) ⊆ mvpActualStackOptimismEvent hH E fallback δ c₁ c₂ := by
    intro sample hs
    exact mvp_sourceStack_optimistic_of_batchEvent hH E sample.1 fallback sample.2
      δ c₁ c₂ hδ hδsmall hc₁ hc₂ hs.2
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  rw [hprod] at hmono
  exact lt_of_lt_of_le hgood hmono
/-- Corrected source allocation, with no batch-event probability premise. -/
theorem mvp_actualStackOptimism_sourceProbability {H K : ℕ}
    (hH : 0 < H) (hK : 0 < K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    1-2*(Fintype.card State : ℝ)*Fintype.card Action*H*K*δp <
      (onlineMDPInitialStackLaw E ρ K).real (mvpActualStackOptimismEvent hH E fallback δp c₁ c₂) := by
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  have hs : 0 < Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have ha : 0 < Fintype.card Action := Fintype.card_pos_iff.mpr inferInstance
  have hd := onlineSourceOptimismDeltaPrime_domain δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδ1 hs ha hH hK
  have hp := mvp_actualStackOptimism_probability hH hK E ρ fallback
    (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K)
    c₁ c₂ hd.1 hd.2 hc₁ hc₂
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, mul_assoc,
    mul_left_comm, mul_comm] using hp

end StatisticalRL.OnlineRL

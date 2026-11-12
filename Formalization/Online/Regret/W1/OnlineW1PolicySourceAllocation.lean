import Formalization.Online.Regret.W1.OnlineW1PolicyProbability

/-! OnlineW1PolicySourceAllocation: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w1PolicySourceStateMeasurable : MeasurableSpace State := ⊤
local instance w1PolicySourceAtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

/-- Source-allocated same-law W₁ policy-variance budget, with the strict
6 SAHK δ′ confidence loss from the two actual events. -/
theorem onlineSourceAllocated_actualW1PolicyBudget_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let δ' := onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - 6 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H * K * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualW1PolicyBudgetEvent H K hH E fallback δ' c₁ c₂) := by
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  have hd := onlineSourceOptimismDeltaPrime_domain δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδone Fintype.card_pos Fintype.card_pos hH hK
  have hp := onlineSequential_actualW1PolicyBudget_strict H K hH hK E ρ fallback δ' c₁ c₂
    hd.1 hd.2 hc₁ hc₂
  rw [onlineMDPRow_card_real] at hp
  simpa only [mul_assoc] using hp
end StatisticalRL.OnlineRL

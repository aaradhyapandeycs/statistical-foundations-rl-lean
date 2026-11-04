import Formalization.Online.Regret.Definitions
import Formalization.Online.Regret.SummedEpisodes
import Formalization.Online.SourceOptimism.SourceOptimismAllocation

/-! Actual-path UCBVI ProbabilityTransfer; no regret-rate theorem is claimed. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]

local instance onlineRegretProbabilityStateMeasurable : MeasurableSpace State := ⊤

/-- Measurability refers to the same induced finite sample space on which the
actual sequential episode law is defined. -/
theorem onlineActualRegretDecompositionEvent_measurable
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ' c₁ c₂ : ℝ) :
    MeasurableSet (onlineActualRegretDecompositionEvent H K hH E fallback δ' c₁ c₂) := by
  classical
  exact (Set.to_countable _).measurableSet

/-- The source-allocated optimism probability transfers to the same-path
four-term decomposition event. The confidence bound is the actual strict
factor-two result; no concentration claim about the terms is made. -/
theorem onlineSourceAllocated_actualRegretDecomposition_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let δ' := onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - 2 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H * K * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualRegretDecompositionEvent H K hH E fallback δ' c₁ c₂) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)
  have hd := onlineSourceOptimismDeltaPrime_domain δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδone Fintype.card_pos Fintype.card_pos hH hK
  have hsub : {sample : (Fin K → State) × OnlineOutcomePath State (K * H) |
      onlineHistoryAllStageTrajectoryOptimism H K E δ' c₁ c₂
        (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
          (K * H) [] sample.2)} ⊆
      onlineActualRegretDecompositionEvent H K hH E fallback δ' c₁ c₂ := by
    intro sample hs
    exact onlineActualRegret_le_four_terms H K hH E sample.1 fallback sample.2 δ' c₁ c₂
      hd.1 hd.2 hc₁ hc₂ hs
  have hmono := measureReal_mono hsub (measure_ne_top ν.rowMeasure _)
  have hprob := onlineSourceAllocated_allStageTrajectoryOptimism_strict H K hH hK E ρ
    fallback δ c₁ c₂ hδ hδone hc₁ hc₂
  exact hprob.trans_le hmono

end StatisticalRL.OnlineRL

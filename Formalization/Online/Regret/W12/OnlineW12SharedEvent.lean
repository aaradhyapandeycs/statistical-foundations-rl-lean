import Formalization.Online.Regret.W12.OnlineW12FullRadiusBudget
import Formalization.Online.Regret.Joint.OnlineW123SharedEvent

/-! Same-experiment suffix proof component: OnlineW12SharedEvent.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w12EventState : MeasurableSpace State := ⊤
local instance w12EventAtom (K n : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

noncomputable def onlineActualW12SharedHistoryEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) : Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
  {sample |
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
    onlineObservedTrueW1Certificates H K E δ history ∧
    onlineObservedW2CoordinateCertificates H K E δ history ∧
    onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂ history}

theorem onlineSequential_actualW12_shared_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    1 - (4 * (Fintype.card State : ℝ) + 6) * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualW12SharedHistoryEvent H K hH E fallback δ c₁ c₂) := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)
  let good1 : Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
    {sample | onlineObservedTrueW1Certificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2)}
  let goodC : Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
    {sample | onlineObservedW2CoordinateCertificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2)}
  let goodO : Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
    {sample | onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2)}
  have h1 := onlineSequential_observedTrueW1Certificates_strict H K hH hK E ρ fallback planner δ hδ (by linarith)
  have hC := onlineSequential_observedW2CoordinateCertificates_strict H K hH hK E ρ fallback planner δ hδ (by linarith)
  have hO := onlineGreedySequential_allStageTrajectoryOptimism_strict H K hH hK E ρ fallback δ c₁ c₂ hδ hδsmall hc₁ hc₂
  have hc1 := measureReal_compl (μ := ν.rowMeasure) ((Set.to_countable good1).measurableSet)
  have hcC := measureReal_compl (μ := ν.rowMeasure) ((Set.to_countable goodC).measurableSet)
  have hcO := measureReal_compl (μ := ν.rowMeasure) ((Set.to_countable goodO).measurableSet)
  have hci := measureReal_compl (μ := ν.rowMeasure) ((Set.to_countable (good1 ∩ (goodC ∩ goodO))).measurableSet)
  rw [probReal_univ] at hc1 hcC hcO hci
  have hu1 := measureReal_union_le (μ := ν.rowMeasure) goodCᶜ goodOᶜ
  have hu2 := measureReal_union_le (μ := ν.rowMeasure) good1ᶜ (goodCᶜ ∪ goodOᶜ)
  have hset : (good1 ∩ (goodC ∩ goodO))ᶜ = good1ᶜ ∪ (goodCᶜ ∪ goodOᶜ) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, not_and_or]
  rw [hset] at hci
  change 1 - 4 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ < ν.rowMeasure.real good1 at h1
  change 1 - 4 * (Fintype.card State : ℝ) * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ < ν.rowMeasure.real goodC at hC
  change 1 - 2 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ < ν.rowMeasure.real goodO at hO
  change 1 - (4 * (Fintype.card State : ℝ) + 6) * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ < ν.rowMeasure.real (good1 ∩ (goodC ∩ goodO))
  nlinarith
end StatisticalRL.OnlineRL

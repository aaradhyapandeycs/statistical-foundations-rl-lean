import Formalization.Online.Regret.Joint.OnlineW123Singleton

/-! One fixed-V*, one fixed-V*², one shared coordinate, and one optimism
event jointly imply the three restricted corrected W₁/W₂/W₃ clauses. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w123StateMeasurable : MeasurableSpace State := ⊤
local instance w123AtomMeasurable (K n : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

noncomputable def onlineActualW123RestrictedEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) : Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
  onlineActualW1RestrictedIotaEvent H K hH E fallback δ c₁ c₂ ∩
    (onlineActualW2RestrictedIotaEvent H K hH E fallback δ c₁ c₂ ∩
      onlineActualW3RestrictedIotaEvent H K hH E fallback δ c₁ c₂)

theorem onlineSequential_actualW123_shared_strict
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    1 - (4 * (Fintype.card State : ℝ) + 10) * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualW123RestrictedEvent H K hH E fallback δ c₁ c₂) := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)
  let good1 : Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
    {sample | onlineObservedTrueW1Certificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2)}
  let good3 : Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
    {sample | onlineObservedW3SquareCertificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2)}
  let goodC : Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
    {sample | onlineObservedW2CoordinateCertificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2)}
  let goodO : Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
    {sample | onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2)}
  let target := onlineActualW123RestrictedEvent H K hH E fallback δ c₁ c₂
  have hk : 0 < K := by omega
  have h1 := onlineSequential_observedTrueW1Certificates_strict H K hH hk E ρ fallback planner δ hδ (by linarith)
  have h3 := onlineSequential_observedW3SquareCertificates_strict H K hH hk E ρ fallback planner δ hδ (by linarith)
  have hC := onlineSequential_observedW2CoordinateCertificates_strict H K hH hk E ρ fallback planner δ hδ (by linarith)
  have hO := onlineGreedySequential_allStageTrajectoryOptimism_strict H K hH hk E ρ fallback δ c₁ c₂ hδ hδsmall hc₁ hc₂
  have hsub : good1 ∩ (good3 ∩ (goodC ∩ goodO)) ⊆ target := by
    intro sample hs
    have hp1 := onlineActualW1_le_policyVarianceBudget H K hH E sample.1 fallback sample.2 δ c₁ c₂
      hδ (by linarith) hs.1 hs.2.2.2
    have hp2 := onlineActualW2_le_policyDifferenceBudget H K hH E sample.1 fallback sample.2 δ c₁ c₂
      hδ (by linarith) (by linarith) (by nlinarith [sq_nonneg c₁]) hs.2.2.1 hs.2.2.2
    have hp3 := onlineActualW3_le_coarseBudget H K hH E sample.1 fallback sample.2 δ c₁ c₂
      hδ (by linarith) (by linarith) (by nlinarith [sq_nonneg c₁]) hs.2.1 hs.2.2.1 hs.2.2.2
    exact ⟨onlineActualW1PolicyBudget_implies_restrictedIota H K hH hK E fallback δ c₁ c₂ hδ hδsmall hp1,
      onlineActualW2PolicyBudget_implies_restrictedIota H K hH hK E fallback δ c₁ c₂ hδ hδsmall hp2,
      onlineActualW3CoarseBudget_implies_restrictedIota H K hH hK E fallback δ c₁ c₂ hδ hδsmall hp3⟩
  have hm := measureReal_mono hsub (measure_ne_top ν.rowMeasure _)
  have hc1 := measureReal_compl (μ := ν.rowMeasure) ((Set.to_countable good1).measurableSet)
  have hc3 := measureReal_compl (μ := ν.rowMeasure) ((Set.to_countable good3).measurableSet)
  have hcC := measureReal_compl (μ := ν.rowMeasure) ((Set.to_countable goodC).measurableSet)
  have hcO := measureReal_compl (μ := ν.rowMeasure) ((Set.to_countable goodO).measurableSet)
  have hci := measureReal_compl (μ := ν.rowMeasure) ((Set.to_countable (good1 ∩ (good3 ∩ (goodC ∩ goodO)))).measurableSet)
  rw [probReal_univ] at hc1 hc3 hcC hcO hci
  have hu1 := measureReal_union_le (μ := ν.rowMeasure) goodCᶜ goodOᶜ
  have hu2 := measureReal_union_le (μ := ν.rowMeasure) good3ᶜ (goodCᶜ ∪ goodOᶜ)
  have hu3 := measureReal_union_le (μ := ν.rowMeasure) good1ᶜ (good3ᶜ ∪ (goodCᶜ ∪ goodOᶜ))
  have hset : (good1 ∩ (good3 ∩ (goodC ∩ goodO)))ᶜ = good1ᶜ ∪ (good3ᶜ ∪ (goodCᶜ ∪ goodOᶜ)) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, not_and_or]
  rw [hset] at hci
  change 1 - 4 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ < ν.rowMeasure.real good1 at h1
  change 1 - 4 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ < ν.rowMeasure.real good3 at h3
  change 1 - 4 * (Fintype.card State : ℝ) * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ < ν.rowMeasure.real goodC at hC
  change 1 - 2 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ < ν.rowMeasure.real goodO at hO
  change 1 - (4 * (Fintype.card State : ℝ) + 10) * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ < ν.rowMeasure.real target
  nlinarith
end StatisticalRL.OnlineRL

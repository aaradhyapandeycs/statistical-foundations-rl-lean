import Formalization.Online.Regret.W1.OnlineW1PolicyVarianceBridge

/-! OnlineW1PolicyProbability: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w1PolicyProbabilityStateMeasurable : MeasurableSpace State := ⊤
local instance w1PolicyProbabilityAtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

noncomputable def onlineActualW1PolicyBudgetEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
  {sample |
    let L := Real.log (1 / (2 * δ))
    let A := (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H
    let R := A * (1 + Real.log (K + 1 : ℝ))
    (∑ k : Fin K, onlineActualEpisodeW1 H K hH E sample.1 fallback sample.2 k δ c₁ c₂) ≤
      (H : ℝ) * (3 * A) +
      Real.sqrt (2 * L * (2 * onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂ +
        2 * onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂)) * Real.sqrt R +
      (2 * H * L / 3) * R}

/-- Both actual-history certificates imply the actual policy-variance budget;
the finite law supplies the union bound. -/
theorem onlineSequential_actualW1PolicyBudget_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    1 - 6 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualW1PolicyBudgetEvent H K hH E fallback δ c₁ c₂) := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)
  let goodW : Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
    {sample | onlineObservedTrueW1Certificates H K E δ
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
        (K * H) [] sample.2)}
  let goodO : Set ((Fin K → State) × OnlineOutcomePath State (K * H)) :=
    {sample | onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
        (K * H) [] sample.2)}
  let target := onlineActualW1PolicyBudgetEvent H K hH E fallback δ c₁ c₂
  have hw := onlineSequential_observedTrueW1Certificates_strict H K hH hK E ρ fallback planner δ hδ (by linarith)
  have ho := onlineGreedySequential_allStageTrajectoryOptimism_strict H K hH hK E ρ fallback δ c₁ c₂ hδ hδsmall hc₁ hc₂
  have hsub : goodW ∩ goodO ⊆ target := by
    intro sample hs
    exact onlineActualW1_le_policyVarianceBudget H K hH E sample.1 fallback sample.2 δ c₁ c₂
      hδ (by linarith) hs.1 hs.2
  have hmono := measureReal_mono hsub (measure_ne_top ν.rowMeasure _)
  have hwcomp := measureReal_compl (μ := ν.rowMeasure) ((Set.to_countable goodW).measurableSet)
  have hocomp := measureReal_compl (μ := ν.rowMeasure) ((Set.to_countable goodO).measurableSet)
  have hintcomp := measureReal_compl (μ := ν.rowMeasure) ((Set.to_countable (goodW ∩ goodO)).measurableSet)
  rw [probReal_univ] at hwcomp hocomp hintcomp
  have hu := measureReal_union_le (μ := ν.rowMeasure) goodWᶜ goodOᶜ
  have hset : (goodW ∩ goodO)ᶜ = goodWᶜ ∪ goodOᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, not_and_or]
  rw [hset] at hintcomp
  change 1 - 6 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ < ν.rowMeasure.real target
  change 1 - 4 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ < ν.rowMeasure.real goodW at hw
  change 1 - 2 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ < ν.rowMeasure.real goodO at ho
  nlinarith
end StatisticalRL.OnlineRL

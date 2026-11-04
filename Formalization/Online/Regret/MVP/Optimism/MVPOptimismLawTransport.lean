import Formalization.Online.Regret.MVP.Optimism.MVPSourceOptimismStatement
import Formalization.Online.Regret.MVP.Optimism.MVPActualStackOptimismProbability

/-! Intermediate law transport. The displayed subset is precisely the
pending actual-history/table identity; it is not an assumption of the
source-facing proposition in MVPSourceOptimismStatementDraft. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action] [Nonempty State]
local instance mvpTransportStateMeasurable : MeasurableSpace State := ⊤
local instance mvpTransportTranscriptMeasurable (H K : ℕ) : MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤
local instance mvpTransportAtomMeasurable (K n : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤

theorem mvp_stackOptimism_to_sequential {H K : ℕ}
    (hH : 0 < H) (hK : 0 < K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hbridge : ∀ (initial : Fin K → State) (data : OnlineMDPRow State Action H × Fin K → State),
      (initial,data) ∈ mvpActualStackOptimismEvent hH E fallback
        (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K) c₁ c₂ →
      mvpHistoryAllStageOptimism (K := K) hH E fallback
        (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K) c₁ c₂
        (onlineMVPActualStackHistory hH initial fallback
          (onlineMVPCommittedGreedyPlanner hH E fallback
            (Real.log (1 / onlineSourceOptimismDeltaPrime δ (Fintype.card State)
              (Fintype.card Action) H K)) c₁ c₂) data (K*H))) :
    let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
    1-2*(Fintype.card State : ℝ)*Fintype.card Action*H*K*δp <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        {sample | mvpHistoryAllStageOptimism (K := K) hH E fallback δp c₁ c₂
          (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
            (K*H) [] sample.2)} := by
  classical
  let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
  let μ := onlineMDPInitialStackLaw E ρ K
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)
  let target : Set (OnlineResetTranscript State Action H K) :=
    {record | mvpHistoryAllStageOptimism (K := K) hH E fallback δp c₁ c₂ record.2}
  let observe := fun sample : (Fin K → State) × (OnlineMDPRow State Action H × Fin K → State) =>
    (sample.1, onlineMVPActualStackHistory hH sample.1 fallback planner sample.2 (K*H))
  let encode := fun sample : (Fin K → State) × OnlineOutcomePath State (K*H) =>
    (sample.1, onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
      (K*H) [] sample.2)
  letI : IsProbabilityMeasure μ := by dsimp [μ, onlineMDPInitialStackLaw, onlineMDPStackLaw]; infer_instance
  have hprob := mvp_actualStackOptimism_sourceProbability hH hK E ρ fallback δ c₁ c₂ hδ hδ1 hc₁ hc₂
  have hsub : mvpActualStackOptimismEvent hH E fallback δp c₁ c₂ ⊆ observe ⁻¹' target := by
    intro sample hs
    exact hbridge sample.1 sample.2 hs
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have hcouple : μ.map observe = ν.rowMeasure.map encode :=
    onlineStack_sequential_transcriptLaw_eq H K hH E ρ fallback planner (K*H) le_rfl
  have hmap : μ.real (observe ⁻¹' target) = ν.rowMeasure.real (encode ⁻¹' target) := by
    have heq := congrArg (fun law : Measure (OnlineResetTranscript State Action H K) => law.real target) hcouple
    simpa only [measureReal_def, Measure.map_apply (measurable_of_countable _)
      ((Set.to_countable target).measurableSet)] using heq
  change 1-2*(Fintype.card State : ℝ)*Fintype.card Action*H*K*δp < ν.rowMeasure.real (encode ⁻¹' target)
  rw [← hmap]
  exact hprob.trans_le hmono
end StatisticalRL.OnlineRL

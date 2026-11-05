import Formalization.Online.Regret.T4.OnlineRegretT4SourceConfidence
import Formalization.Online.Regret.MVP.MVPModelDefinitions

/-! Actual MVP T4 confidence for the same frozen episode policy and realized return. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance mvpT4StateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance mvpT4SampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) := ⊤

noncomputable def mvpActualT4
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{uState,0} State (K*H))
    (L c₁ c₂ : ℝ) : ℝ :=
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
  ∑ k : Fin K, onlineT4EpisodeIncrement H K hH E initial fallback planner path k

theorem mvpActualT4_source_confidence_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (L c₁ c₂ δtail : ℝ)
    (hδ : 0 < δtail) (hδ1 : δtail < 1) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
    1 - 2*δtail < μ.real
      {sample : (Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H) |
        |mvpActualT4 H K hH E sample.1 fallback sample.2 L c₁ c₂| ≤
          Real.sqrt (2*(K : ℝ)*(H : ℝ)^2*Real.log (1/δtail))} := by
  classical
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let X := fun sample : (Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H) =>
    mvpActualT4 H K hH E sample.1 fallback sample.2 L c₁ c₂
  have heq (sample : (Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) :
      (∑ n ∈ Finset.range K, onlineT4PaddedEpisodeY H K hH E fallback planner n sample) = X sample := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [onlineT4PaddedEpisodeY, dif_pos k.isLt]
    rfl
  have hmgf : HasSubgaussianMGF X ((K : ℝ≥0)*(H : ℝ≥0)^2) μ := by
    have h := onlineT4EpisodeSum_hasSubgaussianMGF H K hH E ρ fallback planner
    apply h.congr
    exact Filter.Eventually.of_forall heq
  have hc : 0 < (K : ℝ≥0)*(H : ℝ≥0)^2 := by
    have hKr : 0 < (K : ℝ≥0) := by exact_mod_cast hK
    have hHr : 0 < (H : ℝ≥0) := by exact_mod_cast hH
    exact mul_pos hKr (pow_pos hHr _)
  have ht := StatisticalRL.HasSubgaussianMGF.measure_abs_le_sqrt_gt_of_finite μ X
    ((K : ℝ≥0)*(H : ℝ≥0)^2) hc hmgf δtail hδ hδ1
  simpa only [X, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, mul_assoc] using ht
end StatisticalRL.OnlineRL

import Formalization.Online.Regret.T4.OnlineRegretT4PublicBridge
import Formalization.Probability.FiniteStrictTwoSidedTail

/-! actual source T4 concentration, onlineRL.tex 3802–3818.
The same selected episode policies and same recorded reward paths are used
in the probability law, martingale increments, and public T4 expression. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t4ConfidenceStateMeasurable : MeasurableSpace State :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable
noncomputable local instance t4ConfidenceSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  StatisticalRL.FiniteDistribution.empiricalRowStateMeasurable

theorem onlineActualT4_hasSubgaussianMGF
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    HasSubgaussianMGF
      (fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
        ∑ k : Fin K,
          (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ c₁ c₂).2.2.2)
      ((K : ℝ≥0) * (H : ℝ≥0)^2) μ := by
  dsimp
  have hs := onlineT4EpisodeSum_hasSubgaussianMGF H K hH E ρ fallback
    (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)
  apply hs.congr
  exact Filter.Eventually.of_forall
    (onlineT4PaddedEpisodeSum_eq_publicT4 H K hH E fallback δ c₁ c₂)

theorem onlineActualT4_source_confidence_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    1 - 2 * δ < μ.real {sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) |
      |∑ k : Fin K,
        (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ c₁ c₂).2.2.2| ≤
        Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * Real.log (1 / δ))} := by
  dsimp
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let X := fun sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) =>
    ∑ k : Fin K,
      (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ c₁ c₂).2.2.2
  have hc : 0 < (K : ℝ≥0) * (H : ℝ≥0)^2 := by
    have hK' : 0 < (K : ℝ≥0) := by exact_mod_cast hK
    have hH' : 0 < (H : ℝ≥0) := by exact_mod_cast hH
    exact mul_pos hK' (pow_pos hH' _)
  have ht := StatisticalRL.HasSubgaussianMGF.measure_abs_le_sqrt_gt_of_finite
    μ X ((K : ℝ≥0) * (H : ℝ≥0)^2) hc
    (onlineActualT4_hasSubgaussianMGF H K hH E ρ fallback δ c₁ c₂) δ hδ hδ1
  simpa only [X, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, mul_assoc] using ht

end StatisticalRL.OnlineRL

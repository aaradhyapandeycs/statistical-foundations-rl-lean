import Formalization.Online.QLearning.ActualRegretProcess

namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance regretTailStateMeasurable : MeasurableSpace State := ⊤
local instance regretTailSampleMeasurable (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := ⊤

/-- Strict Azuma tail for the signed, deterministically weighted actual
Q-learning regret residuals. The algorithm and probability law are unchanged. -/
theorem qLearning_actual_weightedRegretResidual_confidence
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (bonus : ℕ → ℝ) (fallback : State) (w : Fin H → ℝ)
    (M : ℝ≥0) (hM : 0 < M) (hweight : ∀ h, |w h| ≤ (M:ℝ))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
    1-δ < μ.real {sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) |
      |∑ n ∈ Finset.range (K*H), qLearningRegretChronologicalY hH E bonus fallback w n sample| ≤
      Real.sqrt (2*((K:ℝ)*(H:ℝ)*((M:ℝ)*(H:ℝ))^2)*Real.log (2/δ))} := by
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (qLearningActualEpisodePlanner hH E bonus) (K*H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let X := fun sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H) =>
    ∑ n ∈ Finset.range (K*H), qLearningRegretChronologicalY hH E bonus fallback w n sample
  let c : ℝ≥0 := ((K*H:ℕ):ℝ≥0)*(M*(H:ℝ≥0))^2
  have hc : 0<c := by dsimp [c]; positivity
  have hm : Measurable X := measurable_of_countable _
  have hs : HasSubgaussianMGF X c μ :=
    qLearning_regretChronologicalSum_hasSubgaussianMGF H K hH E ρ bonus fallback w M hweight
  have ht := StatisticalRL.azuma_subgaussian_strict_two_sided μ X hm c hc hs δ hδ hδ1
  simpa only [c,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_natCast,Nat.cast_mul] using ht

end StatisticalRL.OnlineRL

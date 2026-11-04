import Formalization.Online.Regret.MVP.T6.MVPActualT8Process
import Formalization.Online.Regret.T8.OnlineT8ConditionalVariance

/-! Uncompiled exact conditional variance of the actual MVP square-tail test. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance t6MVPActualT8ConditionalVariance_mvpT8CondState : MeasurableSpace State := ⊤
local instance t6MVPActualT8ConditionalVariance_mvpT8CondSample (H K : ℕ) : MeasurableSpace
    ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := ⊤

noncomputable def mvpT8PaddedRowVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) : ℝ :=
  if n < K*H then
    let observed := onlineT3CommonPrefixObservation H K (K*H) hH fallback planner n sample
    (onlineMDPSuccessorRowLaw E
      (onlineEpisodicChoose H K hH sample.1 fallback planner observed.2)).variance
      (mvpT8PredictableSquare H K hH E fallback L c₁ c₂ n sample.1 observed.2)
  else 0

/-- The row variance of the unsquared retained-table continuation, with the
same predictable prefix and selected row as the square-tail residual. -/
noncomputable def mvpT8PaddedTailVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) : ℝ :=
  if n < K*H then
    let observed := onlineT3CommonPrefixObservation H K (K*H) hH fallback planner n sample
    (onlineMDPSuccessorRowLaw E
      (onlineEpisodicChoose H K hH sample.1 fallback planner observed.2)).variance
      (mvpT8CompletedPrefixTail H hH E fallback L c₁ c₂ n observed.2)
  else 0

theorem mvpT8PaddedRowVariance_le_four_H_sq_tail
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) :
    0 ≤ mvpT8PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample ∧
      mvpT8PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample ≤
        4*(H : ℝ)^2*mvpT8PaddedTailVariance H K hH E fallback planner L c₁ c₂ n sample := by
  classical
  by_cases hn : n < K*H
  · simp only [mvpT8PaddedRowVariance, mvpT8PaddedTailVariance, hn, ↓reduceIte]
    constructor
    · exact FiniteDistribution.variance_nonneg _ _
    · exact onlineW3_square_variance_le _ _ _ (by positivity)
        (mvpT8CompletedPrefixTail_range H hH E fallback L c₁ c₂ hL hc₁ hc₂ n _)
  · simp [mvpT8PaddedRowVariance, mvpT8PaddedTailVariance, hn]

theorem mvpT8PaddedY_sq_condExp_eq_rowVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[(fun sample => (mvpT8PaddedY H K hH E fallback planner L c₁ c₂ n sample)^2) |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ]
      (fun sample => mvpT8PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample) := by
  classical
  by_cases hn : n < K * H
  · let m := K * H - (n + 1)
    have hT : K * H = (m + 1) + n := by dsimp [m]; omega
    let φ := mvpT8PredictableSquare H K hH E fallback L c₁ c₂ n
    have hsig := onlineT3CommonPrefixSigma_eq_splitPrefixSigma H K (K * H) hH E fallback planner (m + 1) n hT
    have hsource' := onlinePredictableTest_conditionalVariance_exact H K hH E ρ fallback planner n m (K * H) φ hT
    have hp : (fun sample => (mvpT8PaddedY H K hH E fallback planner L c₁ c₂ n sample)^2) =
        (fun sample => (onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m φ (hT ▸ sample))^2) := by
      funext sample
      have he := onlinePredictableObservedY_eq_source H K (K * H) hH E fallback planner n m hT φ sample
      simp only [mvpT8PaddedY, hn, ↓reduceIte]
      rw [he]
    have hobs : (fun sample => onlineT3PrefixObservation H K hH fallback planner (m + 1) n (hT ▸ sample)) =
        onlineT3CommonPrefixObservation H K (K * H) hH fallback planner n := by
      funext sample
      exact (onlineT3CommonPrefixObservation_eq_splitPrefix H K (K * H) hH fallback planner (m + 1) n hT sample).symm
    dsimp only
    rw [hsig, hp]
    simpa [mvpT8PaddedRowVariance, hn, φ, ← hobs] using hsource'
  · have hy : mvpT8PaddedY H K hH E fallback planner L c₁ c₂ n = 0 := by
      funext sample
      simp [mvpT8PaddedY, hn]
    have hv : mvpT8PaddedRowVariance H K hH E fallback planner L c₁ c₂ n = 0 := by
      funext sample
      simp [mvpT8PaddedRowVariance, hn]
    simp only [hy, hv, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0)]
    change (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure[0 |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[_] 0
    rw [condExp_zero]
end StatisticalRL.OnlineRL

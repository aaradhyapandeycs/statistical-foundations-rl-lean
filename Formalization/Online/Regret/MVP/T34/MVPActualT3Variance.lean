import Formalization.Online.Regret.MVP.T34.MVPActualT3Process
import Formalization.Online.Regret.MVP.T6.MVPActualT8ConditionalVariance

/-! Conditional variance of the actual predictable MVP T3 residual. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance mvpT3CondState : MeasurableSpace State := ⊤
local instance mvpT3CondSample (H K : ℕ) : MeasurableSpace
    ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := ⊤
theorem mvpT3PaddedY_sq_condExp_eq_rowVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[(fun sample => (mvpT3PaddedY H K hH E fallback planner L c₁ c₂ n sample)^2) |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ]
      (fun sample => mvpT8PaddedTailVariance H K hH E fallback planner L c₁ c₂ n sample) := by
  classical
  by_cases hn : n < K * H
  · let m := K * H - (n + 1)
    have hT : K * H = (m + 1) + n := by dsimp [m]; omega
    let φ := mvpT3PredictableTail H K hH E fallback L c₁ c₂ n
    have hsig := onlineT3CommonPrefixSigma_eq_splitPrefixSigma H K (K * H) hH E fallback planner (m + 1) n hT
    have hsource' := onlinePredictableTest_conditionalVariance_exact H K hH E ρ fallback planner n m (K * H) φ hT
    have hp : (fun sample => (mvpT3PaddedY H K hH E fallback planner L c₁ c₂ n sample)^2) =
        (fun sample => (onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m φ (hT ▸ sample))^2) := by
      funext sample
      have he := onlinePredictableObservedY_eq_source H K (K * H) hH E fallback planner n m hT φ sample
      simp only [mvpT3PaddedY, hn, ↓reduceIte]
      rw [he]
    have hobs : (fun sample => onlineT3PrefixObservation H K hH fallback planner (m + 1) n (hT ▸ sample)) =
        onlineT3CommonPrefixObservation H K (K * H) hH fallback planner n := by
      funext sample
      exact (onlineT3CommonPrefixObservation_eq_splitPrefix H K (K * H) hH fallback planner (m + 1) n hT sample).symm
    dsimp only
    rw [hsig, hp]
    simpa [mvpT8PaddedTailVariance, mvpT3PredictableTail, hn, φ, ← hobs] using hsource'
  · have hy : mvpT3PaddedY H K hH E fallback planner L c₁ c₂ n = 0 := by
      funext sample
      simp [mvpT3PaddedY, hn]
    have hv : mvpT8PaddedTailVariance H K hH E fallback planner L c₁ c₂ n = 0 := by
      funext sample
      simp [mvpT8PaddedTailVariance, hn]
    simp only [hy, hv, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0)]
    change (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure[0 |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[_] 0
    rw [condExp_zero]
end StatisticalRL.OnlineRL

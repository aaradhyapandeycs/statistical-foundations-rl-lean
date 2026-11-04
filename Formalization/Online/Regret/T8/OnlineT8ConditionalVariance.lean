import Formalization.Online.Predictable.OnlinePredictableTestVariance

/-! Actual-law variance and gap proof component: OnlineT8ConditionalVariance.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t8CondState : MeasurableSpace State := ⊤
noncomputable local instance t8CondSample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

theorem onlinePredictableTest_conditionalVariance_exact
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (n m T : ℕ) (φ : (Fin K → State) → List (OnlineMDPRow State Action H × State) → State → ℝ)
    (horizon : T = (m + 1) + n) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner T).rowMeasure
    μ[(fun sample => (onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m φ (horizon ▸ sample))^2) |
      onlineT3SplitPrefixSigma H K hH E fallback planner (m + 1) n T horizon] =ᵐ[μ]
      (fun sample => (onlineMDPSuccessorRowLaw E (onlineEpisodicChoose H K hH sample.1 fallback planner
        (onlineT3PrefixObservation H K hH fallback planner (m + 1) n (horizon ▸ sample)).2)).variance
        (φ sample.1 (onlineT3PrefixObservation H K hH fallback planner (m + 1) n (horizon ▸ sample)).2)) := by
  subst T
  simpa [onlineT3SplitPrefixSigma] using onlinePredictableTest_conditionalVariance H K hH E ρ fallback planner n m φ

theorem onlineT8PaddedY_sq_condExp_eq_rowVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[(fun sample => (onlineT8PaddedY H K hH E fallback planner L c₁ c₂ n sample)^2) |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ]
      (fun sample => onlineT8PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample) := by
  classical
  by_cases hn : n < K * H
  · let m := K * H - (n + 1)
    have hT : K * H = (m + 1) + n := by dsimp [m]; omega
    let φ := onlineT8PredictableSquare H K hH E L c₁ c₂ n
    have hsig := onlineT3CommonPrefixSigma_eq_splitPrefixSigma H K (K * H) hH E fallback planner (m + 1) n hT
    have hsource' := onlinePredictableTest_conditionalVariance_exact H K hH E ρ fallback planner n m (K * H) φ hT
    have hp : (fun sample => (onlineT8PaddedY H K hH E fallback planner L c₁ c₂ n sample)^2) =
        (fun sample => (onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m φ (hT ▸ sample))^2) := by
      funext sample
      have he := onlinePredictableObservedY_eq_source H K (K * H) hH E fallback planner n m hT φ sample
      simp only [onlineT8PaddedY, hn, ↓reduceIte]
      rw [he]
    have hobs : (fun sample => onlineT3PrefixObservation H K hH fallback planner (m + 1) n (hT ▸ sample)) =
        onlineT3CommonPrefixObservation H K (K * H) hH fallback planner n := by
      funext sample
      exact (onlineT3CommonPrefixObservation_eq_splitPrefix H K (K * H) hH fallback planner (m + 1) n hT sample).symm
    dsimp only
    rw [hsig, hp]
    simpa [onlineT8PaddedRowVariance, hn, φ, ← hobs] using hsource'
  · have hy : onlineT8PaddedY H K hH E fallback planner L c₁ c₂ n = 0 := by
      funext sample
      simp [onlineT8PaddedY, hn]
    have hv : onlineT8PaddedRowVariance H K hH E fallback planner L c₁ c₂ n = 0 := by
      funext sample
      simp [onlineT8PaddedRowVariance, hn]
    simp only [hy, hv, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0)]
    change (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure[0 |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[_] 0
    rw [condExp_zero]
end StatisticalRL.OnlineRL

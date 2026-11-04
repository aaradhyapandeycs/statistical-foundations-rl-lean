import Formalization.Online.Regret.Gap.OnlineJ1RowVariance
import Formalization.Online.Regret.T8.OnlineT8ConditionalVariance

/-! Actual-law variance and gap proof component: OnlineJ1ConditionalVariance.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance j1CondState : MeasurableSpace State := ⊤
noncomputable local instance j1CondSample (H K : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤
theorem onlineJ1PaddedY_sq_condExp_eq_rowVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (L c₁ c₂ : ℝ) (n : ℕ) :
    let planner := onlineCappedGreedyPlanner E L c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[(fun sample => (onlineJ1PaddedY H K hH E fallback L c₁ c₂ n sample)^2) |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ]
      (fun sample => onlineJ1PaddedRowVariance H K hH E fallback L c₁ c₂ n sample) := by
  classical
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  dsimp only
  by_cases hn : n < K * H
  · let m := K * H - (n + 1)
    have hT : K * H = (m + 1) + n := by dsimp [m]; omega
    let φ := onlineJ1PredictableGap H K hH E L c₁ c₂ n
    have hsig := onlineT3CommonPrefixSigma_eq_splitPrefixSigma H K (K * H) hH E fallback planner (m + 1) n hT
    have hsource' := onlinePredictableTest_conditionalVariance_exact H K hH E ρ fallback planner n m (K * H) φ hT
    have hp : (fun sample => (onlineJ1PaddedY H K hH E fallback L c₁ c₂ n sample)^2) =
        (fun sample => (onlinePredictableTestResidualAtPrefix H K hH E fallback planner n m φ (hT ▸ sample))^2) := by
      funext sample
      have he := onlinePredictableObservedY_eq_source H K (K * H) hH E fallback planner n m hT φ sample
      simp only [onlineJ1PaddedY, hn, ↓reduceIte]
      rw [he]
    have hobs : (fun sample => onlineT3PrefixObservation H K hH fallback planner (m + 1) n (hT ▸ sample)) =
        onlineT3CommonPrefixObservation H K (K * H) hH fallback planner n := by
      funext sample
      exact (onlineT3CommonPrefixObservation_eq_splitPrefix H K (K * H) hH fallback planner (m + 1) n hT sample).symm
    rw [hsig, hp]
    dsimp [planner] at hobs hsource'
    simpa [onlineJ1PaddedRowVariance, hn, φ, planner, ← hobs] using hsource'
  · have hy : onlineJ1PaddedY H K hH E fallback L c₁ c₂ n = 0 := by
      funext sample
      simp [onlineJ1PaddedY, hn]
    have hv : onlineJ1PaddedRowVariance H K hH E fallback L c₁ c₂ n = 0 := by
      funext sample
      simp [onlineJ1PaddedRowVariance, hn]
    simp only [hy, hv, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0)]
    change (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure[0 |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[_] 0
    rw [condExp_zero]
end StatisticalRL.OnlineRL

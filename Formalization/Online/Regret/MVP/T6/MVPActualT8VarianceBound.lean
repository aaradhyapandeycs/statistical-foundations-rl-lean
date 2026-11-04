import Formalization.Online.Regret.MVP.T6.MVPActualT8Freedman
import Formalization.Online.Regret.MVP.T6.MVPActualTailVariance

/-! Actual-law variance and gap proof component: OnlineT8ActualVariance.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t6MVPActualT8VarianceBound_mvpT8ActualVarState : MeasurableSpace State := ⊤
noncomputable local instance t6MVPActualT8VarianceBound_mvpT8ActualVarSample (H K : ℕ) :
  MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

theorem mvpT8PredictableSecondMomentSum_le_actualT6UCB
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ)
    (hL : 0 ≤ Real.log (1 / δ)) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    ∀ᵐ sample ∂μ, predictableSecondMomentSum μ ℱ
      (mvpT8PaddedY H K hH E fallback planner (Real.log (1 / δ)) c₁ c₂) (K * H) sample ≤
      4 * (H : ℝ)^2 * mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ := by
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δ)) c₁ c₂
  have hs := mvpT8PredictableSecondMomentSum_eq_rowVarianceSum H K hH E ρ fallback planner
    (Real.log (1 / δ)) c₁ c₂ (K * H)
  filter_upwards [hs] with sample hs
  rw [hs]
  calc
    _ ≤ 4 * (H : ℝ)^2 * ∑ n ∈ Finset.range (K * H),
        mvpT8PaddedTailVariance H K hH E fallback planner (Real.log (1 / δ)) c₁ c₂ n sample :=
      mvpT8RowVarianceSum_le_four_H_sq_tail H K hH E fallback planner (Real.log (1 / δ)) c₁ c₂ hL hc₁ hc₂ (K * H) sample
    _ = _ := by rw [mvpTailVarianceSum_eq_actualT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂]
end StatisticalRL.OnlineRL

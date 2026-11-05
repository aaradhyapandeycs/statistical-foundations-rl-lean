import Formalization.Online.Regret.MVP.T34.MVPActualT3Variance
import Formalization.Online.Regret.MVP.T6.MVPActualTailVariance
import Formalization.Online.Regret.MVP.T6.MVPActualT8VarianceSum

/-! The predictable variance sum agrees with the actual MVP true-transition variance. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance mvpT3VarSumState : MeasurableSpace State := ⊤
noncomputable local instance mvpT3VarSumSample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) := ⊤
theorem mvpT3PredictableSecondMomentSum_eq_rowVarianceSum
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    ∀ N, ∀ᵐ sample ∂μ,
      predictableSecondMomentSum μ ℱ (mvpT3PaddedY H K hH E fallback planner L c₁ c₂) N sample =
      ∑ n ∈ Finset.range N, mvpT8PaddedTailVariance H K hH E fallback planner L c₁ c₂ n sample := by
  classical
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := mvpT3PaddedY H K hH E fallback planner L c₁ c₂
  let V := mvpT8PaddedTailVariance H K hH E fallback planner L c₁ c₂
  have hterm (n : ℕ) : μ[fun sample => X n sample ^ 2 | ℱ n] =ᵐ[μ] fun sample => V n sample := by
    simpa [μ, ℱ, X, V, onlineT3ActualPrefixFiltration] using
      (mvpT3PaddedY_sq_condExp_eq_rowVariance H K hH E ρ fallback planner L c₁ c₂ n)
  intro N
  induction N with
  | zero => filter_upwards [] with sample; simp [predictableSecondMomentSum]
  | succ N ih =>
      have hlast := hterm N
      filter_upwards [ih, hlast] with sample hprev hlast
      change (∑ n ∈ Finset.range (N + 1), μ[fun ω => X n ω ^ 2 | ℱ n] sample) =
        ∑ n ∈ Finset.range (N + 1), V n sample
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      change (∑ n ∈ Finset.range N, μ[fun ω => X n ω ^ 2 | ℱ n] sample) =
        ∑ n ∈ Finset.range N, V n sample at hprev
      rw [hprev, hlast]

theorem mvpT3PredictableSecondMomentSum_eq_actualT6UCB
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ c₁ c₂ : ℝ) :
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    ∀ᵐ sample ∂μ, predictableSecondMomentSum μ ℱ
      (mvpT3PaddedY H K hH E fallback planner (Real.log (1/δ)) c₁ c₂) (K*H) sample =
      mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂ := by
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δ)) c₁ c₂
  have hs := mvpT3PredictableSecondMomentSum_eq_rowVarianceSum H K hH E ρ fallback planner
    (Real.log (1/δ)) c₁ c₂ (K*H)
  filter_upwards [hs] with sample hs
  rw [hs, mvpTailVarianceSum_eq_actualT6UCB H K hH E sample.1 fallback sample.2 δ c₁ c₂]
end StatisticalRL.OnlineRL

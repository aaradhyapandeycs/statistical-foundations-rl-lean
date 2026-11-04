import Formalization.Online.Regret.Gap.OnlineJ1ConditionalVariance
import Formalization.Online.Regret.T3.OnlineRegretT3Freedman

/-! Actual-law variance and gap proof component: OnlineJ1VarianceSum.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance j1SumState : MeasurableSpace State := ⊤
noncomputable local instance j1SumSample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

theorem onlineJ1PredictableSecondMomentSum_eq_rowVarianceSum
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (L c₁ c₂ : ℝ) :
    let planner := onlineCappedGreedyPlanner E L c₁ c₂
    let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    ∀ N, ∀ᵐ sample ∂μ,
      predictableSecondMomentSum μ ℱ (onlineJ1PaddedY H K hH E fallback L c₁ c₂) N sample =
      ∑ n ∈ Finset.range N, onlineJ1PaddedRowVariance H K hH E fallback L c₁ c₂ n sample := by
  classical
  dsimp
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := onlineJ1PaddedY H K hH E fallback L c₁ c₂
  let V := onlineJ1PaddedRowVariance H K hH E fallback L c₁ c₂
  have hterm (n : ℕ) : μ[fun sample => X n sample ^ 2 | ℱ n] =ᵐ[μ] fun sample => V n sample := by
    simpa [μ, ℱ, X, V, onlineT3ActualPrefixFiltration] using
      (onlineJ1PaddedY_sq_condExp_eq_rowVariance H K hH E ρ fallback L c₁ c₂ n)
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

theorem onlineJ1RowVarianceSum_le_gapSquare
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State)
    (L c₁ c₂ : ℝ)
    (N : ℕ) (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    (∑ n ∈ Finset.range N, onlineJ1PaddedRowVariance H K hH E fallback L c₁ c₂ n sample) ≤
      ∑ n ∈ Finset.range N, onlineJ1PaddedRowGapSquare H K hH E fallback L c₁ c₂ n sample := by
  apply Finset.sum_le_sum
  intro n hn
  exact (onlineJ1PaddedRowVariance_le_gapSquare H K hH E fallback L c₁ c₂ n sample).2
end StatisticalRL.OnlineRL

namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance j1CapState : MeasurableSpace State := ⊤
noncomputable local instance j1CapSample (H K : ℕ) : MeasurableSpace
    ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

theorem onlineJ1PaddedRowVariance_le_H2
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    onlineJ1PaddedRowVariance H K hH E fallback L c₁ c₂ n sample ≤ (H : ℝ)^2 := by
  classical
  by_cases hn : n < K * H
  · simp only [onlineJ1PaddedRowVariance, hn, ↓reduceIte]
    apply (FiniteDistribution.variance_le_expectation_sq _ _).trans
    apply FiniteDistribution.expectation_le_const
    intro s
    let obs := onlineT3CommonPrefixObservation H K (K * H) hH fallback (onlineCappedGreedyPlanner E L c₁ c₂) n sample
    let gap := onlineJ1RawGap H K hH E L c₁ c₂ n sample.1 obs.2 s
    have h := onlineJ1Clip_range H gap (by positivity)
    change (onlineJ1Clip H gap)^2 ≤ (H : ℝ)^2
    nlinarith
  · simp [onlineJ1PaddedRowVariance, hn]

theorem onlineJ1PredictableSecondMomentSum_le_KH3
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (L c₁ c₂ : ℝ) :
    let planner := onlineCappedGreedyPlanner E L c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    ∀ᵐ sample ∂μ, predictableSecondMomentSum μ ℱ
      (onlineJ1PaddedY H K hH E fallback L c₁ c₂) (K * H) sample ≤
        (K : ℝ) * (H : ℝ)^3 := by
  classical
  dsimp
  have hsum := onlineJ1PredictableSecondMomentSum_eq_rowVarianceSum H K hH E ρ fallback L c₁ c₂ (K * H)
  filter_upwards [hsum] with sample hs
  rw [hs]
  calc
    _ ≤ ∑ _n ∈ Finset.range (K * H), (H : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact onlineJ1PaddedRowVariance_le_H2 H K hH E fallback L c₁ c₂ n sample
    _ = (K : ℝ) * (H : ℝ)^3 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
end StatisticalRL.OnlineRL

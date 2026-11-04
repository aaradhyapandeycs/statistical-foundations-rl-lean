import Formalization.Online.Regret.MVP.T6.MVPActualT8ConditionalVariance
import Formalization.Online.Regret.T3.OnlineRegretT3Freedman

/-! Actual-law variance and gap proof component: OnlineT8VarianceSum.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t6MVPActualT8VarianceSum_mvpT8SumState : MeasurableSpace State := ⊤
noncomputable local instance t6MVPActualT8VarianceSum_mvpT8SumSample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

theorem mvpT8PredictableSecondMomentSum_eq_rowVarianceSum
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    ∀ N, ∀ᵐ sample ∂μ,
      predictableSecondMomentSum μ ℱ (mvpT8PaddedY H K hH E fallback planner L c₁ c₂) N sample =
      ∑ n ∈ Finset.range N, mvpT8PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample := by
  classical
  dsimp
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := mvpT8PaddedY H K hH E fallback planner L c₁ c₂
  let V := mvpT8PaddedRowVariance H K hH E fallback planner L c₁ c₂
  have hterm (n : ℕ) : μ[fun sample => X n sample ^ 2 | ℱ n] =ᵐ[μ] fun sample => V n sample := by
    simpa [μ, ℱ, X, V, onlineT3ActualPrefixFiltration] using
      (mvpT8PaddedY_sq_condExp_eq_rowVariance H K hH E ρ fallback planner L c₁ c₂ n)
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

theorem mvpT8RowVarianceSum_le_four_H_sq_tail
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (N : ℕ) (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    (∑ n ∈ Finset.range N, mvpT8PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample) ≤
      4 * (H : ℝ)^2 * ∑ n ∈ Finset.range N, mvpT8PaddedTailVariance H K hH E fallback planner L c₁ c₂ n sample := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  exact (mvpT8PaddedRowVariance_le_four_H_sq_tail H K hH E fallback planner L c₁ c₂ hL hc₁ hc₂ n sample).2
end StatisticalRL.OnlineRL

namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State : Type*} {Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance t6MVPActualT8VarianceSum_mvpT8CapState : MeasurableSpace State := ⊤
noncomputable local instance t6MVPActualT8VarianceSum_mvpT8CapSample (H K : ℕ) : MeasurableSpace
    ((Fin K → State) × OnlineOutcomePath.{_, 0} State (K * H)) := ⊤

theorem mvpT8PaddedRowVariance_le_H4
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{_, 0} State (K * H)) :
    mvpT8PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample ≤ (H : ℝ)^4 := by
  classical
  by_cases hn : n < K * H
  · simp only [mvpT8PaddedRowVariance, hn, ↓reduceIte]
    apply (FiniteDistribution.variance_le_expectation_sq _ _).trans
    apply FiniteDistribution.expectation_le_const
    intro s
    have h := mvpT8PredictableSquare_range H K hH E fallback L c₁ c₂ hL hc₁ hc₂ n sample.1
      (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner n sample).2 s
    have hH0 : 0 ≤ (H : ℝ)^2 := by positivity
    nlinarith
  · simp [mvpT8PaddedRowVariance, hn]

theorem mvpT8PredictableSecondMomentSum_le_KH5
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    ∀ᵐ sample ∂μ, predictableSecondMomentSum μ ℱ
      (mvpT8PaddedY H K hH E fallback planner L c₁ c₂) (K * H) sample ≤
        (K : ℝ) * (H : ℝ)^5 := by
  classical
  dsimp
  have hsum := mvpT8PredictableSecondMomentSum_eq_rowVarianceSum H K hH E ρ fallback planner L c₁ c₂ (K * H)
  filter_upwards [hsum] with sample hs
  rw [hs]
  calc
    _ ≤ ∑ _n ∈ Finset.range (K * H), (H : ℝ)^4 := by
      apply Finset.sum_le_sum
      intro n hn
      exact mvpT8PaddedRowVariance_le_H4 H K hH E fallback planner L c₁ c₂ hL hc₁ hc₂ n sample
    _ = (K : ℝ) * (H : ℝ)^5 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
end StatisticalRL.OnlineRL

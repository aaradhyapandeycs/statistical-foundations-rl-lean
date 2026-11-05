import Formalization.Online.Regret.MVP.T34.MVPActualT3VarianceSum

/-! Deterministic horizon bound for the predictable MVP T3 variance sum. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance mvpT3CapState : MeasurableSpace State := ⊤
noncomputable local instance mvpT3CapSample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) := ⊤

theorem mvpT3PaddedTailVariance_le_H2
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) :
    mvpT8PaddedTailVariance H K hH E fallback planner L c₁ c₂ n sample ≤ (H : ℝ)^2 := by
  classical
  by_cases hn : n < K*H
  · simp only [mvpT8PaddedTailVariance, hn, ↓reduceIte]
    apply (FiniteDistribution.variance_le_expectation_sq _ _).trans
    apply FiniteDistribution.expectation_le_const
    intro s
    have h := mvpT8CompletedPrefixTail_range H hH E fallback L c₁ c₂ hL hc₁ hc₂ n
      (onlineT3CommonPrefixObservation H K (K*H) hH fallback planner n sample).2 s
    have hh : 0 ≤ (H : ℝ) := by positivity
    nlinarith
  · simp [mvpT8PaddedTailVariance, hn]

theorem mvpT3PredictableSecondMomentSum_le_KH3
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
    let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
    ∀ᵐ sample ∂μ, predictableSecondMomentSum μ ℱ
      (mvpT3PaddedY H K hH E fallback planner L c₁ c₂) (K*H) sample ≤ (K : ℝ)*(H : ℝ)^3 := by
  classical
  dsimp
  have hsum := mvpT3PredictableSecondMomentSum_eq_rowVarianceSum H K hH E ρ fallback planner L c₁ c₂ (K*H)
  filter_upwards [hsum] with sample hs
  rw [hs]
  calc
    _ ≤ ∑ _n ∈ Finset.range (K*H), (H : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact mvpT3PaddedTailVariance_le_H2 H K hH E fallback planner L c₁ c₂ hL hc₁ hc₂ n sample
    _ = (K : ℝ)*(H : ℝ)^3 := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
end StatisticalRL.OnlineRL

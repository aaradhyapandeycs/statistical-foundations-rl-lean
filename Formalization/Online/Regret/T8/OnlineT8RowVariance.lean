import Formalization.Online.Regret.T8.OnlineT8Range
import Formalization.Online.Regret.T3.OnlineRegretT3ConditionalVariance

/-! Actual-law variance and gap proof component: OnlineT8RowVariance.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t8RowStateMeasurable : MeasurableSpace State := ⊤

noncomputable def onlineT8PaddedRowVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  if n < K * H then
    let observed := onlineT3CommonPrefixObservation H K (K * H) hH fallback planner n sample
    (onlineMDPSuccessorRowLaw E
      (onlineEpisodicChoose H K hH sample.1 fallback planner observed.2)).variance
      (onlineT8PredictableSquare H K hH E L c₁ c₂ n sample.1 observed.2)
  else 0

theorem onlineT8PaddedRowVariance_le_four_H_sq_T3
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    0 ≤ onlineT8PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample ∧
      onlineT8PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample ≤
        4 * (H : ℝ)^2 * onlineT3PaddedRowVariance H K hH E fallback planner L c₁ c₂ n sample := by
  classical
  by_cases hn : n < K * H
  · simp only [onlineT8PaddedRowVariance, onlineT3PaddedRowVariance, hn, ↓reduceDIte, ↓reduceIte]
    constructor
    · exact FiniteDistribution.variance_nonneg _ _
    · exact onlineW3_square_variance_le _ _ _ (by positivity)
        (onlineT3CompletedPrefixTail_range H K hH E _ (n / H) ⟨n % H, Nat.mod_lt n hH⟩ L c₁ c₂ hL hc₁ hc₂)
  · simp [onlineT8PaddedRowVariance, onlineT3PaddedRowVariance, hn]
end StatisticalRL.OnlineRL

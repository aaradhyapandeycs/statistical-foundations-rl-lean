import Formalization.Online.Regret.Gap.OnlineJ1Variance
import Formalization.Online.Regret.T3.OnlineRegretT3ConditionalVariance

/-! Actual-law variance and gap proof component: OnlineJ1RowVariance.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance j1RowState : MeasurableSpace State := ⊤

noncomputable def onlineJ1RawGap
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (L c₁ c₂ : ℝ) (n : ℕ) (_initial : Fin K → State)
    (history : List (OnlineMDPRow State Action H × State)) (s : State) : ℝ :=
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let h : Fin H := ⟨n % H, Nat.mod_lt n hH⟩
  onlineT3CompletedPrefixTail E history (n / H) h L c₁ c₂ s -
    onlineT4PolicyTailAtPrefix H hH E planner (n / H) h history s

noncomputable def onlineJ1PaddedRowVariance
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  if n < K * H then
    let observed := onlineT3CommonPrefixObservation H K (K * H) hH fallback planner n sample
    (onlineMDPSuccessorRowLaw E (onlineEpisodicChoose H K hH sample.1 fallback planner observed.2)).variance
      (onlineJ1PredictableGap H K hH E L c₁ c₂ n sample.1 observed.2)
  else 0

noncomputable def onlineJ1PaddedRowGapSquare
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  if n < K * H then
    let observed := onlineT3CommonPrefixObservation H K (K * H) hH fallback planner n sample
    (onlineMDPSuccessorRowLaw E (onlineEpisodicChoose H K hH sample.1 fallback planner observed.2)).expectation
      (fun s => (onlineJ1RawGap H K hH E L c₁ c₂ n sample.1 observed.2 s)^2)
  else 0

theorem onlineJ1PaddedRowVariance_le_gapSquare
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    0 ≤ onlineJ1PaddedRowVariance H K hH E fallback L c₁ c₂ n sample ∧
      onlineJ1PaddedRowVariance H K hH E fallback L c₁ c₂ n sample ≤
        onlineJ1PaddedRowGapSquare H K hH E fallback L c₁ c₂ n sample := by
  classical
  by_cases hn : n < K * H
  · simp only [onlineJ1PaddedRowVariance, onlineJ1PaddedRowGapSquare, hn, ↓reduceIte]
    constructor
    · exact FiniteDistribution.variance_nonneg _ _
    · exact onlineJ1_clipped_variance_le_gap_square _ H (by positivity) _ _
  · simp [onlineJ1PaddedRowVariance, onlineJ1PaddedRowGapSquare, hn]
end StatisticalRL.OnlineRL

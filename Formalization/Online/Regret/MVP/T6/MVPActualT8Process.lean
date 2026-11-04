import Formalization.Online.Regret.MVP.Model.OnlineMVPActualSampler
import Formalization.Online.Predictable.OnlinePredictableObservedProcess
import Formalization.Online.Regret.T3.OnlineRegretT3PaddedProcess
import Formalization.Online.Regret.W3.OnlineW3SquareVariance

/-! Uncompiled actual MVP T8 martingale skeleton. The test is determined by
the completed-episode prefix and the retained-batch table, and the causal
planner is a parameter. No concentration or variance certificate is assumed. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance t6MVPActualT8Process_mvpT8StateMeasurable : MeasurableSpace State := ⊤

noncomputable def mvpT8CompletedPrefixTail
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (n : ℕ)
    (history : List (OnlineMDPRow State Action H × State)) : State → ℝ :=
  onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂
    (onlineMVPHistoryPlanningStages hH E fallback (history.take ((n/H)*H))) (n%H+1)

noncomputable def mvpT8PredictableSquare
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (n : ℕ) (_initial : Fin K → State)
    (history : List (OnlineMDPRow State Action H × State)) (s : State) : ℝ :=
  (mvpT8CompletedPrefixTail H hH E fallback L c₁ c₂ n history s)^2

noncomputable def mvpT8PaddedY
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) : ℝ :=
  if n < K*H then onlinePredictableObservedY H K (K*H) hH E fallback planner n
    (mvpT8PredictableSquare H K hH E fallback L c₁ c₂ n) sample else 0

theorem mvpT8CompletedPrefixTail_range
    (H : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (n : ℕ) (history : List (OnlineMDPRow State Action H × State)) (s : State) :
    0 ≤ mvpT8CompletedPrefixTail H hH E fallback L c₁ c₂ n history s ∧
      mvpT8CompletedPrefixTail H hH E fallback L c₁ c₂ n history s ≤ H := by
  simpa [mvpT8CompletedPrefixTail, onlineCappedBackwardValueAt] using
    onlineCappedBackwardValue_range (H : ℝ) L c₁ c₂ (by positivity) hL hc₁ hc₂
      ((onlineMVPHistoryPlanningStages hH E fallback (history.take ((n/H)*H))).drop (n%H+1)) s

theorem mvpT8PredictableSquare_range
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (n : ℕ) (initial : Fin K → State) (history : List (OnlineMDPRow State Action H × State)) (s : State) :
    0 ≤ mvpT8PredictableSquare H K hH E fallback L c₁ c₂ n initial history s ∧
      mvpT8PredictableSquare H K hH E fallback L c₁ c₂ n initial history s ≤ (H : ℝ)^2 := by
  have hv := mvpT8CompletedPrefixTail_range H hH E fallback L c₁ c₂ hL hc₁ hc₂ n history s
  dsimp [mvpT8PredictableSquare]
  constructor
  · positivity
  · nlinarith

theorem mvpT8PaddedY_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
    μ[mvpT8PaddedY H K hH E fallback planner L c₁ c₂ n |
      onlineT3CommonPrefixSigma H K (K*H) hH fallback planner n] =ᵐ[μ] 0 := by
  dsimp
  by_cases hn : n < K*H
  · have heq : mvpT8PaddedY H K hH E fallback planner L c₁ c₂ n =
      onlinePredictableObservedY H K (K*H) hH E fallback planner n
        (mvpT8PredictableSquare H K hH E fallback L c₁ c₂ n) := by
      funext sample
      simp [mvpT8PaddedY, hn]
    rw [heq]
    exact onlinePredictableObservedY_condExp_zero H K (K*H) hH E ρ fallback planner n
      (K*H-(n+1)) (by omega) (mvpT8PredictableSquare H K hH E fallback L c₁ c₂ n)
  · have heq : mvpT8PaddedY H K hH E fallback planner L c₁ c₂ n = 0 := by
      funext sample
      simp [mvpT8PaddedY, hn]
    rw [heq, condExp_zero]

theorem mvpT8PaddedY_measurable_next
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ) (n : ℕ) :
    Measurable[onlineT3CommonPrefixSigma H K (K*H) hH fallback planner (n+1)]
      (mvpT8PaddedY H K hH E fallback planner L c₁ c₂ n) := by
  by_cases hn : n < K*H
  · have heq : mvpT8PaddedY H K hH E fallback planner L c₁ c₂ n =
      onlinePredictableObservedY H K (K*H) hH E fallback planner n
        (mvpT8PredictableSquare H K hH E fallback L c₁ c₂ n) := by
      funext sample
      simp [mvpT8PaddedY, hn]
    rw [heq]
    exact onlinePredictableObservedY_measurable_next H K (K*H) hH E fallback planner n _
  · have heq : mvpT8PaddedY H K hH E fallback planner L c₁ c₂ n = 0 := by
      funext sample
      simp [mvpT8PaddedY, hn]
    rw [heq]
    exact measurable_const

theorem mvpT8PaddedY_abs_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) :
    |mvpT8PaddedY H K hH E fallback planner L c₁ c₂ n sample| ≤ (H : ℝ)^2 := by
  classical
  unfold mvpT8PaddedY
  split_ifs with hn
  · unfold onlinePredictableObservedY onlinePredictableTestFromObservedPrefix
    split
    · simp
    · rename_i row successor hrec
      have hrange (s : State) := mvpT8PredictableSquare_range H K hH E fallback L c₁ c₂
        hL hc₁ hc₂ n
        (onlineT3CommonPrefixObservation H K (K*H) hH fallback planner (n+1) sample).1
        ((onlineT3CommonPrefixObservation H K (K*H) hH fallback planner (n+1) sample).2.take n) s
      have hm0 := (onlineMDPSuccessorRowLaw E row).expectation_nonneg (fun s => (hrange s).1)
      have hmH := (onlineMDPSuccessorRowLaw E row).expectation_le_const (fun s => (hrange s).2)
      have hy := hrange successor
      apply abs_le.mpr
      constructor <;> linarith
  · simp
end StatisticalRL.OnlineRL

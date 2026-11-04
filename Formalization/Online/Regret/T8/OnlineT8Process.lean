import Formalization.Online.Predictable.OnlinePredictableObservedProcess
import Formalization.Online.Regret.T3.OnlineRegretT3PaddedProcess
import Formalization.Online.Regret.W3.OnlineW3SquareVariance

/-! Actual-law variance and gap proof component: OnlineT8Process.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t8ProcessStateMeasurable : MeasurableSpace State := ⊤

noncomputable def onlineT8PredictableSquare
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (L c₁ c₂ : ℝ) (n : ℕ) (_initial : Fin K → State)
    (history : List (OnlineMDPRow State Action H × State)) (s : State) : ℝ :=
  (onlineT3CompletedPrefixTail E history (n / H) ⟨n % H, Nat.mod_lt n hH⟩ L c₁ c₂ s)^2

noncomputable def onlineT8PaddedY
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  if n < K * H then
    onlinePredictableObservedY H K (K * H) hH E fallback planner n
      (onlineT8PredictableSquare H K hH E L c₁ c₂ n) sample
  else 0

theorem onlineT8PredictableSquare_range
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (n : ℕ) (initial : Fin K → State) (history : List (OnlineMDPRow State Action H × State)) (s : State) :
    0 ≤ onlineT8PredictableSquare H K hH E L c₁ c₂ n initial history s ∧
      onlineT8PredictableSquare H K hH E L c₁ c₂ n initial history s ≤ (H : ℝ)^2 := by
  have h := onlineCappedBackwardValue_range (H : ℝ) L c₁ c₂ (by positivity) hL hc₁ hc₂
    ((List.ofFn (fun j : Fin H => onlineHistoryPlanningStage E (history.take ((n / H) * H)) j)).drop (n % H + 1)) s
  dsimp [onlineT8PredictableSquare, onlineT3CompletedPrefixTail]
  constructor
  · positivity
  · nlinarith

theorem onlineT8PaddedY_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[onlineT8PaddedY H K hH E fallback planner L c₁ c₂ n |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ] 0 := by
  dsimp
  by_cases hn : n < K * H
  · have heq : onlineT8PaddedY H K hH E fallback planner L c₁ c₂ n =
      onlinePredictableObservedY H K (K * H) hH E fallback planner n
        (onlineT8PredictableSquare H K hH E L c₁ c₂ n) := by
      funext sample
      simp [onlineT8PaddedY, hn]
    rw [heq]
    exact onlinePredictableObservedY_condExp_zero H K (K * H) hH E ρ fallback planner n
      (K * H - (n + 1)) (by omega) (onlineT8PredictableSquare H K hH E L c₁ c₂ n)
  · have heq : onlineT8PaddedY H K hH E fallback planner L c₁ c₂ n = 0 := by
      funext sample
      simp [onlineT8PaddedY, hn]
    rw [heq, condExp_zero]

theorem onlineT8PaddedY_measurable_next
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ) (n : ℕ) :
    Measurable[onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (n + 1)]
      (onlineT8PaddedY H K hH E fallback planner L c₁ c₂ n) := by
  by_cases hn : n < K * H
  · have heq : onlineT8PaddedY H K hH E fallback planner L c₁ c₂ n =
      onlinePredictableObservedY H K (K * H) hH E fallback planner n
        (onlineT8PredictableSquare H K hH E L c₁ c₂ n) := by
      funext sample
      simp [onlineT8PaddedY, hn]
    rw [heq]
    exact onlinePredictableObservedY_measurable_next H K (K * H) hH E fallback planner n _
  · have heq : onlineT8PaddedY H K hH E fallback planner L c₁ c₂ n = 0 := by
      funext sample
      simp [onlineT8PaddedY, hn]
    rw [heq]
    exact measurable_const
end StatisticalRL.OnlineRL

import Formalization.Online.Regret.MVP.T6.MVPActualT8Process

/-! Actual predictable unsquared continuation residual for the MVP T3 estimate. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance mvpT3ProcessState : MeasurableSpace State := ⊤

noncomputable def mvpT3PredictableTail
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (n : ℕ) (_initial : Fin K → State)
    (history : List (OnlineMDPRow State Action H × State)) (s : State) : ℝ :=
  mvpT8CompletedPrefixTail H hH E fallback L c₁ c₂ n history s

noncomputable def mvpT3PaddedY
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) : ℝ :=
  if n < K*H then onlinePredictableObservedY H K (K*H) hH E fallback planner n
    (mvpT3PredictableTail H K hH E fallback L c₁ c₂ n) sample else 0

theorem mvpT3PredictableTail_range
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (n : ℕ) (initial : Fin K → State) (history : List (OnlineMDPRow State Action H × State)) (s : State) :
    0 ≤ mvpT3PredictableTail H K hH E fallback L c₁ c₂ n initial history s ∧
      mvpT3PredictableTail H K hH E fallback L c₁ c₂ n initial history s ≤ H := by
  exact mvpT8CompletedPrefixTail_range H hH E fallback L c₁ c₂ hL hc₁ hc₂ n history s

theorem mvpT3PaddedY_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (n : ℕ) :
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
    μ[mvpT3PaddedY H K hH E fallback planner L c₁ c₂ n |
      onlineT3CommonPrefixSigma H K (K*H) hH fallback planner n] =ᵐ[μ] 0 := by
  dsimp
  by_cases hn : n < K*H
  · have heq : mvpT3PaddedY H K hH E fallback planner L c₁ c₂ n =
      onlinePredictableObservedY H K (K*H) hH E fallback planner n
        (mvpT3PredictableTail H K hH E fallback L c₁ c₂ n) := by
      funext sample
      simp [mvpT3PaddedY, hn]
    rw [heq]
    exact onlinePredictableObservedY_condExp_zero H K (K*H) hH E ρ fallback planner n
      (K*H-(n+1)) (by omega) (mvpT3PredictableTail H K hH E fallback L c₁ c₂ n)
  · have heq : mvpT3PaddedY H K hH E fallback planner L c₁ c₂ n = 0 := by
      funext sample
      simp [mvpT3PaddedY, hn]
    rw [heq, condExp_zero]

theorem mvpT3PaddedY_measurable_next
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (L c₁ c₂ : ℝ) (n : ℕ) :
    Measurable[onlineT3CommonPrefixSigma H K (K*H) hH fallback planner (n+1)]
      (mvpT3PaddedY H K hH E fallback planner L c₁ c₂ n) := by
  by_cases hn : n < K*H
  · have heq : mvpT3PaddedY H K hH E fallback planner L c₁ c₂ n =
      onlinePredictableObservedY H K (K*H) hH E fallback planner n
        (mvpT3PredictableTail H K hH E fallback L c₁ c₂ n) := by
      funext sample
      simp [mvpT3PaddedY, hn]
    rw [heq]
    exact onlinePredictableObservedY_measurable_next H K (K*H) hH E fallback planner n _
  · have heq : mvpT3PaddedY H K hH E fallback planner L c₁ c₂ n = 0 := by
      funext sample
      simp [mvpT3PaddedY, hn]
    rw [heq]
    exact measurable_const

theorem mvpT3PaddedY_abs_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) :
    |mvpT3PaddedY H K hH E fallback planner L c₁ c₂ n sample| ≤ (H : ℝ) := by
  classical
  unfold mvpT3PaddedY
  split_ifs with hn
  · unfold onlinePredictableObservedY onlinePredictableTestFromObservedPrefix
    split
    · simp
    · rename_i row successor hrec
      have hrange (s : State) := mvpT3PredictableTail_range H K hH E fallback L c₁ c₂
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

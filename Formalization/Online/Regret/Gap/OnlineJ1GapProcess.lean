import Formalization.Online.Predictable.OnlinePredictableObservedProcess
import Formalization.Online.Regret.T8.OnlineT8ConditionalVariance
import Formalization.Online.Regret.W1.OnlineW1PolicyVarianceBridge

/-! Actual-law variance and gap proof component: OnlineJ1GapProcess.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance j1StateMeasurable : MeasurableSpace State := ⊤

noncomputable def onlineJ1Clip (H x : ℝ) : ℝ := max 0 (min H x)

theorem onlineJ1Clip_range (H x : ℝ) (hH : 0 ≤ H) :
    0 ≤ onlineJ1Clip H x ∧ onlineJ1Clip H x ≤ H := by
  exact ⟨le_max_left _ _, max_le hH (min_le_left _ _)⟩

theorem onlineJ1Clip_eq_of_mem (H x : ℝ) (hx0 : 0 ≤ x) (hxH : x ≤ H) :
    onlineJ1Clip H x = x := by
  simp [onlineJ1Clip, min_eq_right hxH, max_eq_right hx0]

theorem onlineJ1Clip_sq_le (H x : ℝ) (hH : 0 ≤ H) :
    (onlineJ1Clip H x)^2 ≤ x^2 := by
  by_cases hx : 0 ≤ x
  · have hclip := onlineJ1Clip_range H x hH
    have hlex : onlineJ1Clip H x ≤ x := max_le hx (min_le_right _ _)
    nlinarith
  · have hclip : onlineJ1Clip H x = 0 := by
      unfold onlineJ1Clip
      rw [max_eq_left]
      exact (min_le_right H x).trans (le_of_lt (lt_of_not_ge hx))
    rw [hclip]
    simpa using sq_nonneg x

/-- Gap test uses two tables frozen at the same completed episode prefix:
optimistic capped continuation and true value of the deployed greedy policy. -/
noncomputable def onlineJ1PredictableGap
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (L c₁ c₂ : ℝ) (n : ℕ) (_initial : Fin K → State)
    (history : List (OnlineMDPRow State Action H × State)) (s : State) : ℝ :=
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let h : Fin H := ⟨n % H, Nat.mod_lt n hH⟩
  let U := onlineT3CompletedPrefixTail E history (n / H) h L c₁ c₂
  let P := onlineT4PolicyTailAtPrefix H hH E planner (n / H) h history
  onlineJ1Clip H (U s - P s)

noncomputable def onlineJ1PaddedY
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) : ℝ :=
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  if n < K * H then
    onlinePredictableObservedY H K (K * H) hH E fallback planner n
      (onlineJ1PredictableGap H K hH E L c₁ c₂ n) sample
  else 0

theorem onlineJ1PaddedY_condExp_zero
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (L c₁ c₂ : ℝ) (n : ℕ) :
    let planner := onlineCappedGreedyPlanner E L c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
    μ[onlineJ1PaddedY H K hH E fallback L c₁ c₂ n |
      onlineT3CommonPrefixSigma H K (K * H) hH fallback planner n] =ᵐ[μ] 0 := by
  dsimp
  by_cases hn : n < K * H
  · have heq : onlineJ1PaddedY H K hH E fallback L c₁ c₂ n =
      onlinePredictableObservedY H K (K * H) hH E fallback (onlineCappedGreedyPlanner E L c₁ c₂) n
        (onlineJ1PredictableGap H K hH E L c₁ c₂ n) := by
      funext sample
      simp [onlineJ1PaddedY, hn]
    rw [heq]
    exact onlinePredictableObservedY_condExp_zero H K (K * H) hH E ρ fallback
      (onlineCappedGreedyPlanner E L c₁ c₂) n (K * H - (n + 1)) (by omega)
      (onlineJ1PredictableGap H K hH E L c₁ c₂ n)
  · have heq : onlineJ1PaddedY H K hH E fallback L c₁ c₂ n = 0 := by
      funext sample
      simp [onlineJ1PaddedY, hn]
    rw [heq, condExp_zero]
end StatisticalRL.OnlineRL

namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance j1BoundsState : MeasurableSpace State := ⊤

theorem onlineJ1PaddedY_measurable_next
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (n : ℕ) :
    let planner := onlineCappedGreedyPlanner E L c₁ c₂
    Measurable[onlineT3CommonPrefixSigma H K (K * H) hH fallback planner (n + 1)]
      (onlineJ1PaddedY H K hH E fallback L c₁ c₂ n) := by
  dsimp
  by_cases hn : n < K * H
  · have heq : onlineJ1PaddedY H K hH E fallback L c₁ c₂ n =
      onlinePredictableObservedY H K (K * H) hH E fallback (onlineCappedGreedyPlanner E L c₁ c₂) n
        (onlineJ1PredictableGap H K hH E L c₁ c₂ n) := by
      funext sample
      simp [onlineJ1PaddedY, hn]
    rw [heq]
    exact onlinePredictableObservedY_measurable_next H K (K * H) hH E fallback
      (onlineCappedGreedyPlanner E L c₁ c₂) n _
  · have heq : onlineJ1PaddedY H K hH E fallback L c₁ c₂ n = 0 := by
      funext sample
      simp [onlineJ1PaddedY, hn]
    rw [heq]
    exact measurable_const

theorem onlineJ1PaddedY_abs_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (L c₁ c₂ : ℝ) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    |onlineJ1PaddedY H K hH E fallback L c₁ c₂ n sample| ≤ (H : ℝ) := by
  classical
  unfold onlineJ1PaddedY
  split_ifs with hn
  · unfold onlinePredictableObservedY onlinePredictableTestFromObservedPrefix
    dsimp only
    split
    · simp
    · rename_i row successor hrec
      have hrange (s : State) : 0 ≤ onlineJ1PredictableGap H K hH E L c₁ c₂ n
          (onlineT3CommonPrefixObservation H K (K * H) hH fallback (onlineCappedGreedyPlanner E L c₁ c₂) (n + 1) sample).1
          ((onlineT3CommonPrefixObservation H K (K * H) hH fallback (onlineCappedGreedyPlanner E L c₁ c₂) (n + 1) sample).2.take n) s ∧
          onlineJ1PredictableGap H K hH E L c₁ c₂ n
          (onlineT3CommonPrefixObservation H K (K * H) hH fallback (onlineCappedGreedyPlanner E L c₁ c₂) (n + 1) sample).1
          ((onlineT3CommonPrefixObservation H K (K * H) hH fallback (onlineCappedGreedyPlanner E L c₁ c₂) (n + 1) sample).2.take n) s ≤ H := by
        exact onlineJ1Clip_range H _ (by positivity)
      have hm0 := (onlineMDPSuccessorRowLaw E row).expectation_nonneg (fun s => (hrange s).1)
      have hmH := (onlineMDPSuccessorRowLaw E row).expectation_le_const (fun s => (hrange s).2)
      have hy := hrange successor
      apply abs_le.mpr
      constructor <;> linarith
  · simp
end StatisticalRL.OnlineRL

import Formalization.Online.Regret.T8.OnlineT8Process

/-! Actual-law variance and gap proof component: OnlineT8Range.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance t8RangeStateMeasurable : MeasurableSpace State := ⊤

theorem onlineT8PaddedY_abs_le
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (n : ℕ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    |onlineT8PaddedY H K hH E fallback planner L c₁ c₂ n sample| ≤ (H : ℝ)^2 := by
  classical
  unfold onlineT8PaddedY
  split_ifs with hn
  · unfold onlinePredictableObservedY onlinePredictableTestFromObservedPrefix
    split
    · simp
    · rename_i row successor hrec
      have hrange (s : State) := onlineT8PredictableSquare_range H K hH E L c₁ c₂ hL hc₁ hc₂ n
        (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (n + 1) sample).1
        ((onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (n + 1) sample).2.take n) s
      have hm0 := (onlineMDPSuccessorRowLaw E row).expectation_nonneg (fun s => (hrange s).1)
      have hmH := (onlineMDPSuccessorRowLaw E row).expectation_le_const (fun s => (hrange s).2)
      have hy := hrange successor
      apply abs_le.mpr
      constructor <;> linarith
  · simp
end StatisticalRL.OnlineRL

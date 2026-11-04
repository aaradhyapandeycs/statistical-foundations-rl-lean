import Formalization.Online.Regret.T4.OnlineRegretT4SourceStep
import Mathlib.Algebra.BigOperators.Fin

/-! exact episode sum of the actual source T4 steps.
No episode-level concentration theorem is asserted here. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t4EpisodeSumStateMeasurable : MeasurableSpace State := ⊤

/-- The actual return minus the same selected policy's trajectory value is
the sum of its actual, conditionally centered transition residuals. -/
theorem onlineT4EpisodeIncrement_eq_sumActualStep
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    onlineT4EpisodeIncrement H K hH E sample.1 fallback planner sample.2 k =
      ∑ h : Fin H, onlineT4ActualStep H K hH E fallback planner k h sample := by
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
  let state := onlineT4EpisodeState H K sample.1 fallback history k.val
  let g := planner (history.take (k.val * H))
  let D := onlineFixedPolicyStages E g
  have hid := onlineSequentialEpisode_selectedPolicy_noise_identity
    H K hH E sample.1 fallback planner sample.2 k
  change onlineT4EpisodeIncrement H K hH E sample.1 fallback planner sample.2 k =
    ∑ n ∈ Finset.range H,
      if hn : n < H then
        DecisionStage.trajectoryValue (D.drop (n + 1)) (state (n + 1)) -
          ((E ⟨n, hn⟩).transition (state n)
            (onlineT4PlayedAction H K hH sample.1 fallback planner sample.2 k ⟨n, hn⟩)).expectation
            (DecisionStage.trajectoryValue (D.drop (n + 1)))
      else 0 at hid
  rw [hid, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro h hh
  simp only [dif_pos h.isLt]
  have hs := onlineT4ActualStep_eq_policy_noise H K hH E fallback planner k h sample
  have hv : onlineT4PolicyTailAtPrefix H hH E planner k.val h history =
      DecisionStage.trajectoryValue (D.drop (h.val + 1)) := by
    unfold onlineT4PolicyTailAtPrefix
    rw [onlineT4SelectedStages_eq_fixed]
  change onlineT4ActualStep H K hH E fallback planner k h sample =
    onlineT4PolicyTailAtPrefix H hH E planner k.val h history (state (h.val + 1)) -
      ((E h).transition (state h.val)
        (onlineT4PlayedAction H K hH sample.1 fallback planner sample.2 k h)).expectation
        (onlineT4PolicyTailAtPrefix H hH E planner k.val h history) at hs
  rw [hv] at hs
  exact hs.symm

end StatisticalRL.OnlineRL

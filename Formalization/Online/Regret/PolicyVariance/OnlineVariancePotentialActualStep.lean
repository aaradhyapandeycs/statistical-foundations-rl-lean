import Formalization.Online.Regret.PolicyVariance.OnlineVariancePotentialCentering
import Formalization.Online.Regret.PolicyVariance.OnlineFrozenEpisodeVariance
import Formalization.Online.Regret.T4.OnlineRegretT4SourceStep

/-! Actual-law variance and gap proof component: OnlineVariancePotentialActualStep.
This module supplies an intermediate proof, not the complete T56 theorem. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance varianceActualStepStateMeasurable : MeasurableSpace State := ⊤

theorem onlineVariancePotentialTest_take
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ) (initial : Fin K → State)
    (history : List (OnlineMDPRow State Action H × State)) (n : ℕ) (hcut : k.val * H ≤ n) :
    onlineVariancePotentialTest H K hH E k h L c₁ c₂ initial (history.take n) =
      onlineVariancePotentialTest H K hH E k h L c₁ c₂ initial history := by
  unfold onlineVariancePotentialTest
  have hpolicy : onlineCappedEpisodePolicy H hH E (history.take n) k.val L c₁ c₂ =
      onlineCappedEpisodePolicy H hH E history k.val L c₁ c₂ := by
    funext t s
    dsimp only [onlineCappedEpisodePolicy]
    rw [List.take_take, Nat.min_eq_left hcut]
  rw [hpolicy]

theorem onlineVariancePotentialTest_terminal
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ) (initial : Fin K → State)
    (history : List (OnlineMDPRow State Action H × State)) (hterminal : h.val + 1 = H) :
    onlineVariancePotentialTest H K hH E k h L c₁ c₂ initial history = 0 := by
  unfold onlineVariancePotentialTest
  have hlen : (EnvironmentStage.controlled (List.ofFn E)
      (onlineCappedEpisodePolicy H hH E history k.val L c₁ c₂)).length = H := by
    rw [onlineControlledStages_length]
    simp
  have hdrop : (EnvironmentStage.controlled (List.ofFn E)
      (onlineCappedEpisodePolicy H hH E history k.val L c₁ c₂)).drop (h.val + 1) = [] := by
    apply List.drop_eq_nil_of_le
    rw [hlen, hterminal]
  dsimp only
  rw [hdrop]
  funext s
  exact finiteTrajectoryVariancePotential_nil s

/-- Identify the generic predictable-test residual with the true selected
row's potential residual along the same episode. -/
theorem onlineVariancePotentialResidual_eq_actual_noise
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (k : Fin K) (h : Fin H) (L c₁ c₂ : ℝ)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :
    let planner := onlineCappedGreedyPlanner E L c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
    let state := onlineT4EpisodeState H K sample.1 fallback history k.val
    let V := onlineVariancePotentialTest H K hH E k h L c₁ c₂ sample.1 history
    onlineVariancePotentialResidual H K hH E fallback planner k h L c₁ c₂ sample =
      ((E h).transition (state h.val)
        (onlineT4PlayedAction H K hH sample.1 fallback planner sample.2 k h)).expectation V -
          V (state (h.val + 1)) := by
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
  let state := onlineT4EpisodeState H K sample.1 fallback history k.val
  let V := onlineVariancePotentialTest H K hH E k h L c₁ c₂ sample.1 history
  let n := k.val * H + h.val
  have hn : n < history.length := by
    have hlen := onlineSequentialPathHistory_length
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2
    change n < (onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2).length
    rw [hlen]
    simp only [List.length_nil, zero_add]
    calc
      n < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  let record := history.get ⟨n, hn⟩
  let θ := onlineVariancePotentialTest H K hH E k h L c₁ c₂
  have hlen : (history.take n).length = n := by simp only [List.length_take, Nat.min_eq_left hn.le]
  have hobs : (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (n + 1) sample).2 =
      history.take n ++ [(record.1, record.2)] := by
    simpa only [record, Prod.mk.eta] using (List.take_concat_get' history n hn).symm
  have hread := onlinePredictableTestFromObservedPrefix_append H K E n θ
    (history.take n) record.1 record.2
    (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (n + 1) sample) hlen hobs
  have hstep : onlineVariancePotentialResidual H K hH E fallback planner k h L c₁ c₂ sample =
      (onlineMDPSuccessorRowLaw E record.1).expectation V - V record.2 := by
    change onlinePredictableTestFromObservedPrefix H K E n θ
      (onlineT3CommonPrefixObservation H K (K * H) hH fallback planner (n + 1) sample) = _
    rw [hread]
    simp only [θ, V, onlineT3CommonPrefixObservation,
      onlineVariancePotentialTest_take H K hH E k h L c₁ c₂ sample.1 history n (Nat.le_add_right _ _)]
  have hrow := onlineSequentialEpisode_actual_row H K hH E sample.1 fallback planner sample.2 k h
  change record.1 = (h, (state h.val, planner (history.take (k.val * H)) h (state h.val))) at hrow
  have hlaw : onlineMDPSuccessorRowLaw E record.1 =
      (E h).transition (state h.val) (onlineT4PlayedAction H K hH sample.1 fallback planner sample.2 k h) := by
    rw [hrow, onlineT4PlayedAction_eq_selected H K hH E sample.1 fallback planner sample.2 k h]
    rfl
  have hnext : V (state (h.val + 1)) = V record.2 := by
    by_cases hh : h.val + 1 < H
    · apply congrArg V
      exact onlineSequentialEpisode_successor_state H K hH sample.1 fallback planner sample.2 k h hh
    · have ht : h.val + 1 = H := by omega
      have hv : V = 0 := onlineVariancePotentialTest_terminal H K hH E k h L c₁ c₂ sample.1 history ht
      simp only [hv, Pi.zero_apply]
  change onlineVariancePotentialResidual H K hH E fallback planner k h L c₁ c₂ sample =
    ((E h).transition (state h.val) (onlineT4PlayedAction H K hH sample.1 fallback planner sample.2 k h)).expectation V -
      V (state (h.val + 1))
  rw [hstep, hlaw, ← hnext]
end StatisticalRL.OnlineRL

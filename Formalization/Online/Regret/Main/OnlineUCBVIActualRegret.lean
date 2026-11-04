import Formalization.Online.Regret.T0.OnlineT0ActualConfidence
import Formalization.Online.Regret.T0.OnlineT0ActualGapIdentity
import Formalization.Online.Regret.T4.OnlineRegretT4Telescope

/-! Actual-path regret bridges for corrected zero counts and fixed ties. The T0 event premise is explicit; no confidence claim is made here. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

private theorem onlineMain_greedy_length (es : List (EnvironmentStage State Action)) :
    (EnvironmentStage.greedyStages es).length = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [EnvironmentStage.greedyStages, List.length_cons] using congrArg Nat.succ ih

/-- Every realized policy has nonnegative value and the true optimal policy's
value is at most H; this bound requires no optimism or concentration event. -/
theorem onlineActualEpisodeRegret_le_horizon
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{uState, 0} State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) :
    onlineActualEpisodeRegret H K hH E initial fallback path k δ c₁ c₂ ≤ H := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  have hopt : DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E)) (initial k) ≤ H := by
    rw [DecisionStage.trajectoryValue_eq_backwardValue]
    simpa only [onlineMain_greedy_length, List.length_ofFn] using
      DecisionStage.backwardValue_le_length (EnvironmentStage.greedyStages (List.ofFn E)) (initial k)
  have hpolicy : 0 ≤ onlineCappedEpisodePolicyValue H hH E history k.val (initial k)
      (Real.log (1 / δ)) c₁ c₂ := by
    unfold onlineCappedEpisodePolicyValue
    rw [DecisionStage.trajectoryValue_eq_backwardValue]
    exact DecisionStage.backwardValue_nonneg _ _
  change DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E)) (initial k) -
    onlineCappedEpisodePolicyValue H hH E history k.val (initial k) (Real.log (1 / δ)) c₁ c₂ ≤ H
  linarith

/-- Unconditional small-sample bound, including K=1 where source iota is zero. -/
theorem onlineActualRegret_sum_le_KH
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{uState, 0} State (K * H))
    (δ c₁ c₂ : ℝ) :
    (∑ k : Fin K, onlineActualEpisodeRegret H K hH E initial fallback path k δ c₁ c₂) ≤
      (K : ℝ) * H := by
  calc
    _ ≤ ∑ _k : Fin K, (H : ℝ) := Finset.sum_le_sum (fun k _ =>
      onlineActualEpisodeRegret_le_horizon H K hH E initial fallback path δ c₁ c₂ k)
    _ = _ := by simp

/-- The actual stage-zero suffix begins at this episode's reset state. -/
theorem onlineT0ActualSuffixState_zero_eq_initial
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{uState, 0} State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) :
    onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k 0 = initial k := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  have hlen : (history.take (k.val * H)).length = k.val * H :=
    onlineSequential_episodePrefix_length H K hH E initial fallback planner path k.val k.isLt.le
  have hreset := onlineEpisodicCurrentState_reset H K hH initial fallback (history.take (k.val * H)) k hlen
  simpa [onlineT0ActualSuffixState, onlineT4EpisodeState, planner, history] using hreset

/-- At stage zero, actual optimism compares regret to the same-policy actual
stage gap, on the same completed-history table. -/
theorem onlineActualEpisodeRegret_le_stageZeroGap_of_optimism
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath.{uState, 0} State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path)) :
    onlineActualEpisodeRegret H K hH E initial fallback path k δ c₁ c₂ ≤
      onlineActualStagePolicyGap H K hH E initial fallback path δ c₁ c₂ ⟨0, hH⟩ k := by
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  have hopt := (hoptimism k ⟨0, hH⟩).1 (initial k)
  have hstate := onlineT0ActualSuffixState_zero_eq_initial H K hH E initial fallback path δ c₁ c₂ k
  rw [onlineActualStagePolicyGap_eq_suffix_gap]
  dsimp only
  rw [hstate]
  change DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E)) (initial k) -
      onlineCappedEpisodePolicyValue H hH E history k.val (initial k) (Real.log (1 / δ)) c₁ c₂ ≤
    onlineCappedBackwardValueAt H (Real.log (1 / δ)) c₁ c₂ (onlinePreEpisodePlanningStages E history k.val) 0 (initial k) -
      onlineCappedEpisodePolicyValue H hH E history k.val (initial k) (Real.log (1 / δ)) c₁ c₂
  apply sub_le_sub_right
  simpa [planner, history] using hopt

/-- The canonical actual T0 event supplies both optimism and the stage-zero
budget on exactly the same sample. -/
theorem onlineActualRegret_sum_le_sourceT0_of_event
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) (δ c₁ c₂ : ℝ)
    (hs : sample ∈ onlineActualT0OptimisticUniformEvent H K hH E fallback δ c₁ c₂) :
    (∑ k : Fin K, onlineActualEpisodeRegret H K hH E sample.1 fallback sample.2 k δ c₁ c₂) ≤
      onlineActualT0SourceUpper H K hH E fallback sample δ c₁ c₂ := by
  have hpoint : (∑ k : Fin K, onlineActualEpisodeRegret H K hH E sample.1 fallback sample.2 k δ c₁ c₂) ≤
      ∑ k : Fin K, onlineActualStagePolicyGap H K hH E sample.1 fallback sample.2 δ c₁ c₂ ⟨0, hH⟩ k := by
    apply Finset.sum_le_sum
    intro k hk
    exact onlineActualEpisodeRegret_le_stageZeroGap_of_optimism H K hH E sample.1 fallback sample.2 δ c₁ c₂ k hs.1
  exact hpoint.trans (hs.2 ⟨0, hH⟩)
end StatisticalRL.OnlineRL

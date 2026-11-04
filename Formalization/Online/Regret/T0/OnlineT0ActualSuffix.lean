import Formalization.Online.Regret.T0.OnlineT0SuffixTelescope
import Formalization.Online.Regret.T4.OnlineT4SuffixTelescope
import Formalization.Online.Regret.FixedOptimalSplit

/-! Same-experiment suffix proof component: OnlineT0ActualSuffix.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

noncomputable def onlineT0ActualSuffixStage
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) (h : Fin H) : OnlineObservedPlanningStage State Action :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  onlineHistoryPlanningStage E (history.take (k.val * H)) h

noncomputable def onlineT0ActualSuffixState
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) (n : ℕ) : State :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  onlineT4EpisodeState H K initial fallback history k.val n

noncomputable def onlineT0ActualSuffixAction
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) (n : ℕ) : Action :=
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  if hn : n < H then onlineT4PlayedAction H K hH initial fallback planner path k ⟨n, hn⟩
  else Classical.choice ((E ⟨0, hH⟩).action_nonempty)

/-- On the actual recorded history the greedy action satisfies every stage's
same pre-episode capped backup. -/
theorem onlineT0ActualSuffix_greedy
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (k : Fin K) :
    let stage := onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k
    let state := onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k
    let action := onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k
    ∀ h : Fin H, letI : Nonempty Action := (stage h).environment.action_nonempty
      onlineCappedStageQ H (Real.log (1 / δ)) c₁ c₂ (stage h)
        (onlineCappedBackwardValue H (Real.log (1 / δ)) c₁ c₂ ((List.ofFn stage).drop (h.val + 1)))
        (state h.val) (action h.val) =
      actionMaximum (onlineCappedStageQ H (Real.log (1 / δ)) c₁ c₂ (stage h)
        (onlineCappedBackwardValue H (Real.log (1 / δ)) c₁ c₂ ((List.ofFn stage).drop (h.val + 1)))
        (state h.val)) := by
  classical
  dsimp only
  intro h
  letI : Nonempty Action := (E h).action_nonempty
  have hmax := onlineSequentialEpisode_backup_is_greedy H K hH E initial fallback path k h
    (Real.log (1 / δ)) c₁ c₂ (E h).action_nonempty
  have hstage : onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k =
      fun h => onlineHistoryPlanningStage E ((onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback
        (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂)) (K * H) [] path).take (k.val * H)) h := by
    funext h
    rfl
  rw [hstage]
  simpa [onlineT0ActualSuffixStage, onlineT0ActualSuffixState, onlineT0ActualSuffixAction,
    onlinePreEpisodePlanningStages, onlineT4EpisodeState, onlineT4PlayedAction,
    List.take_take, Nat.min_self, h.isLt] using hmax

/-- Actual gap at stage j is bounded by the three pathwise suffix terms plus
the true-policy suffix return noise on the same selected episode policy. -/
theorem onlineT0ActualSuffix_gap_le_terms
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂) (k : Fin K) (j : Fin H) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let stage := onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k
    let state := onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k
    let action := onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k
    let policy := onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂
    onlineCappedBackwardValueAt H (Real.log (1 / δ)) c₁ c₂
        (onlinePreEpisodePlanningStages E history k.val) j.val (state j.val) -
      DecisionStage.trajectoryValue ((EnvironmentStage.controlled (List.ofFn E) policy).drop j.val) (state j.val) ≤
      (∑ n ∈ Finset.Ico j.val H, onlineCappedEpisodeT1 H stage state action (Real.log (1 / δ)) c₁ c₂ n) +
      (∑ n ∈ Finset.Ico j.val H, onlineCappedEpisodeT2 H stage state action (Real.log (1 / δ)) c₁ c₂ n) +
      (∑ n ∈ Finset.Ico j.val H, onlineCappedEpisodeT3 H stage state action (Real.log (1 / δ)) c₁ c₂ n) +
      onlineT4SuffixEpisodeIncrement H K hH E fallback planner j.val k (initial, path) := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let stage := onlineT0ActualSuffixStage H K hH E initial fallback path δ c₁ c₂ k
  let state := onlineT0ActualSuffixState H K hH E initial fallback path δ c₁ c₂ k
  let action := onlineT0ActualSuffixAction H K hH E initial fallback path δ c₁ c₂ k
  have ht := onlineCappedEpisode_realized_suffix_telescope H j.val j.isLt.le stage state action δ c₁ c₂
    hδ hδsmall hc₁ hc₂ (fun h => (stage h).environment.action_nonempty)
    (onlineT0ActualSuffix_greedy H K hH E initial fallback path δ c₁ c₂ k)
  have hsum : (∑ n ∈ Finset.Ico j.val H, onlineCappedEpisodeTelescopeSummand H stage state action (Real.log (1 / δ)) c₁ c₂ n) =
      (∑ n ∈ Finset.Ico j.val H, onlineCappedEpisodeT1 H stage state action (Real.log (1 / δ)) c₁ c₂ n) +
      (∑ n ∈ Finset.Ico j.val H, onlineCappedEpisodeT2 H stage state action (Real.log (1 / δ)) c₁ c₂ n) +
      (∑ n ∈ Finset.Ico j.val H, onlineCappedEpisodeT3 H stage state action (Real.log (1 / δ)) c₁ c₂ n) +
      (∑ n ∈ Finset.Ico j.val H, onlineCappedEpisodeReward H E state action n) := by
    calc
      _ = ∑ n ∈ Finset.Ico j.val H,
          (onlineCappedEpisodeT1 H stage state action (Real.log (1 / δ)) c₁ c₂ n +
           onlineCappedEpisodeT2 H stage state action (Real.log (1 / δ)) c₁ c₂ n +
           onlineCappedEpisodeT3 H stage state action (Real.log (1 / δ)) c₁ c₂ n +
           onlineCappedEpisodeReward H E state action n) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnH := (Finset.mem_Ico.mp hn).2
        simp [onlineCappedEpisodeTelescopeSummand, onlineCappedEpisodeT1, onlineCappedEpisodeT2,
          onlineCappedEpisodeT3, onlineCappedEpisodeReward, stage, onlineT0ActualSuffixStage,
          onlineHistoryPlanningStage, hnH] <;> ring_nf
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hvalue : onlineCappedBackwardValueAt H (Real.log (1 / δ)) c₁ c₂
      (onlinePreEpisodePlanningStages E history k.val) j.val (state j.val) =
      onlineCappedEpisodeValueAlongPath stage state H (Real.log (1 / δ)) c₁ c₂ j.val := by
    have hstage : stage = fun h => onlineHistoryPlanningStage E (history.take (k.val * H)) h := by
      funext h
      rfl
    rw [hstage]
    rfl
  have hT4 := onlineT4SuffixEpisodeIncrement_eq_return_sub_value H K hH E fallback planner j.val j.isLt.le k (initial, path)
  have hpolicy : EnvironmentStage.controlled (List.ofFn E)
      (onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂) =
      onlineFixedPolicyStages E (planner (history.take (k.val * H))) := by
    simpa [onlineCappedEpisodePolicy, onlineT4SelectedEpisodePolicy, planner] using
      onlineT4SelectedStages_eq_fixed H hH E planner history k.val
  have hreward : (∑ n ∈ Finset.Ico j.val H, onlineCappedEpisodeReward H E state action n) =
      ∑ n ∈ Finset.Ico j.val H, if hn : n < H then
        (E ⟨n, hn⟩).reward (state n) (planner (history.take (k.val * H)) ⟨n, hn⟩ (state n)) else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnH := (Finset.mem_Ico.mp hn).2
    simp only [onlineCappedEpisodeReward, dif_pos hnH]
    simp only [action, onlineT0ActualSuffixAction, dif_pos hnH]
    change (E ⟨n, hnH⟩).reward (state n)
      (onlineT4PlayedAction H K hH initial fallback planner path k ⟨n, hnH⟩) = _
    rw [onlineT4PlayedAction_eq_selected H K hH E initial fallback planner path k ⟨n, hnH⟩]
    rfl
  have hT4' : onlineT4SuffixEpisodeIncrement H K hH E fallback planner j.val k (initial, path) =
      (∑ n ∈ Finset.Ico j.val H, onlineCappedEpisodeReward H E state action n) -
        DecisionStage.trajectoryValue ((EnvironmentStage.controlled (List.ofFn E)
          (onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂)).drop j.val) (state j.val) := by
    rw [hreward, hpolicy]
    simpa [planner, history, state, onlineT0ActualSuffixState] using hT4
  dsimp only
  rw [hvalue, hT4']
  rw [hsum] at ht
  linarith
end StatisticalRL.OnlineRL

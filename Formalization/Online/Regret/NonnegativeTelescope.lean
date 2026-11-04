import Formalization.Online.Regret.Telescope

/-! Nonnegative-parameter telescopes for the corrected zero-count UCBVI backup. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The pathwise telescope uses only nonnegative log and bonus parameters. -/
theorem onlineCappedEpisode_realized_telescope_nonnegative
    (H : ℕ) (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hAction : ∀ h : Fin H, Nonempty Action)
    (hgreedy : ∀ h : Fin H,
      letI : Nonempty Action := hAction h
      onlineCappedStageQ (H : ℝ) (L) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (L) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1))) (state h.val) (action h.val) =
      actionMaximum (onlineCappedStageQ (H : ℝ) (L) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (L) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1))) (state h.val))) :
    onlineCappedEpisodeValueAlongPath stage state (H : ℝ) (L) c₁ c₂ 0 ≤
      ∑ n ∈ Finset.range H,
        onlineCappedEpisodeTelescopeSummand H stage state action (L) c₁ c₂ n := by
  let stages := List.ofFn stage
  let v : ℕ → ℝ := fun n =>
    onlineCappedBackwardValue (H : ℝ) (L) c₁ c₂
      (stages.drop n) (state n)
  let g : ℕ → ℝ := fun n =>
    onlineCappedEpisodeTelescopeSummand H stage state action (L) c₁ c₂ n
  have hstep : ∀ n, v n ≤ g n + v (n + 1) := by
    intro n
    by_cases hn : n < H
    · let h : Fin H := ⟨n, hn⟩
      have hdrop : stages.drop n = stage h :: stages.drop (n + 1) := by
        have hi : n < stages.length := by simpa [stages] using hn
        simpa only [stages, List.getElem_ofFn] using List.drop_eq_getElem_cons hi
      have hnext : ∀ x, 0 ≤ onlineCappedBackwardValue (H : ℝ) (L) c₁ c₂
          (stages.drop (n + 1)) x := by
        exact fun x => (onlineCappedBackwardValue_range (H : ℝ) (L) c₁ c₂
          (by positivity) hL hc₁ hc₂  (stages.drop (n + 1)) x).1
      have hrow := onlineCappedStage_greedy_step_telescope (H : ℝ) (L) c₁ c₂
        (stage h) (stages.drop (n + 1)) (state n) (state (n + 1)) (action n)
        (by positivity) hL hc₁ hc₂ (hAction h) (hgreedy h)
      have hcurrent : v n =
          onlineCappedBackwardValue (H : ℝ) (L) c₁ c₂
            (stage h :: stages.drop (n + 1)) (state n) := by
        simp only [v]
        rw [hdrop]
      have hgoal := hrow
      rw [← hcurrent] at hgoal
      simpa [g, hn, h, v, stages, onlineCappedEpisodeTelescopeSummand] using hgoal
    · have hlen : stages.length = H := by simp [stages]
      have hdropn : stages.drop n = [] := List.drop_eq_nil_of_le (by omega)
      have hdropSucc : stages.drop (n + 1) = [] :=
        List.drop_eq_nil_of_le (by omega)
      have hvn : v n = 0 := by simp [v, hdropn, onlineCappedBackwardValue]
      have hvSucc : v (n + 1) = 0 :=
        by simp [v, hdropSucc, onlineCappedBackwardValue]
      simp [g, onlineCappedEpisodeTelescopeSummand, hn, hvn, hvSucc]
  have hterminal : v H = 0 := by
    have hlen : stages.length = H := by simp [stages]
    have hdrop : stages.drop H = [] := List.drop_eq_nil_of_le (by omega)
    simp [v, hdrop, onlineCappedBackwardValue]
  have htel := onlineRealSequence_telescope_from H 0 v g hstep
  have hresult : v 0 ≤ ∑ n ∈ Finset.range H, g n := by
    simpa [hterminal] using htel
  simpa [v, g, stages, onlineCappedEpisodeValueAlongPath] using hresult


/-- The actual sequential episode satisfies the same telescope for every nonnegative parameter choice. -/
theorem onlineSequentialEpisode_realized_telescope_nonnegative
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K)
    (L c₁ c₂ : ℝ) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    let planner := onlineCappedGreedyPlanner E (L) c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    let prehist := history.take (k.val * H)
    let stage : Fin H → OnlineObservedPlanningStage State Action :=
      fun h => onlineHistoryPlanningStage E prehist h
    let state : ℕ → State := fun n =>
      onlineEpisodicCurrentState H K initial fallback
        (history.take (k.val * H + n))
    let action : ℕ → Action := fun n =>
      if hn : n < H then
        (history.get ⟨k.val * H + n, by
          have hlen := onlineSequentialPathHistory_length
            (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
          rw [hlen]
          simp only [List.length_nil, zero_add]
          calc
            k.val * H + n < k.val * H + H := Nat.add_lt_add_left hn _
            _ = (k.val + 1) * H := by rw [Nat.succ_mul]
            _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
      else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
    onlineCappedEpisodeValueAlongPath stage state (H : ℝ) (L) c₁ c₂ 0 ≤
      ∑ n ∈ Finset.range H,
        onlineCappedEpisodeTelescopeSummand H stage state action
          (L) c₁ c₂ n := by
  classical
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let planner := onlineCappedGreedyPlanner E (L) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let prehist := history.take (k.val * H)
  let stages := onlinePreEpisodePlanningStages E prehist k.val
  let stage : Fin H → OnlineObservedPlanningStage State Action :=
    fun h => onlineHistoryPlanningStage E prehist h
  let state : ℕ → State := fun n =>
    onlineEpisodicCurrentState H K initial fallback
      (history.take (k.val * H + n))
  let action : ℕ → Action := fun n =>
    if hn : n < H then
      (history.get ⟨k.val * H + n, by
        have hlen := onlineSequentialPathHistory_length
          (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
        rw [hlen]
        simp only [List.length_nil, zero_add]
        calc
          k.val * H + n < k.val * H + H := Nat.add_lt_add_left hn _
          _ = (k.val + 1) * H := by rw [Nat.succ_mul]
          _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1.2.2
    else Classical.choice ((E ⟨0, hH⟩).action_nonempty)
  have hgreedy : ∀ h : Fin H, letI : Nonempty Action := (E h).action_nonempty
      onlineCappedStageQ (H : ℝ) (L) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (L) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1)))
        (state h.val) (action h.val) =
      actionMaximum (onlineCappedStageQ (H : ℝ) (L) c₁ c₂
        (stage h) (onlineCappedBackwardValue (H : ℝ) (L) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1))) (state h.val)) := by
    intro h
    letI : Nonempty Action := (E h).action_nonempty
    have hprefixlen := onlineSequential_episodePrefix_length H K hH E initial
      fallback planner path k.val k.isLt.le
    have hpre : prehist.take (k.val * H) = prehist := by
      rw [← hprefixlen, List.take_length]
    have hmax := onlineSequentialEpisode_backup_is_greedy H K hH E initial fallback
      path k h (L) c₁ c₂ (E h).action_nonempty
    have hmax' := hmax
    simp only [onlinePreEpisodePlanningStages] at hmax'
    rw [hpre] at hmax'
    simpa [planner, history, prehist, stages, stage, state, action, h.isLt] using hmax'
  simpa [planner, history, prehist, stages, stage, state, action] using
    onlineCappedEpisode_realized_telescope_nonnegative H stage state action L c₁ c₂
      hL hc₁ hc₂ (fun h => (E h).action_nonempty) hgreedy


end StatisticalRL.OnlineRL

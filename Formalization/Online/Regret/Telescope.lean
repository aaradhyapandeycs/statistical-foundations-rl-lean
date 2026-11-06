import Formalization.Online.SourceOptimism.GreedySequentialTrajectoryOptimism
import Formalization.Online.Regret.Definitions

/-! Actual-path UCBVI Telescope; no regret-rate theorem is claimed. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- One corrected capped row backup is bounded by its empirical mean plus the
analysis charge. The zero-count case uses `Q=cap` and charge `cap`, with only
the source nonnegative-reward and nonnegative-continuation facts. -/
theorem onlineCappedStageQ_le_analysisBackup
    (cap L c₁ c₂ : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (next : State → ℝ) (hnext : ∀ x, 0 ≤ next x)
    (s : State) (a : Action) :
    onlineCappedStageQ cap L c₁ c₂ stage next s a ≤
      stage.environment.reward s a +
        (onlineObservedPlanningRow stage s a).expectation next +
        onlineRegretAnalysisCharge cap L c₁ c₂ stage next s a := by
  by_cases hN : 0 < (stage.observations s a).length
  · rw [onlineCappedStageQ_positive_count cap L c₁ c₂ stage next s a hN]
    simp only [onlineRegretAnalysisCharge, hN, ↓reduceDIte]
    calc
      min (stage.environment.reward s a +
          (onlineObservedPlanningRow stage s a).expectation next +
          c₁ * Real.sqrt ((onlineObservedPlanningRow stage s a).variance next * L /
            (stage.observations s a).length) +
          c₂ * cap * L / (stage.observations s a).length) cap ≤ _ := min_le_left _ _
      _ = stage.environment.reward s a +
          (onlineObservedPlanningRow stage s a).expectation next +
          (c₁ * Real.sqrt ((onlineObservedPlanningRow stage s a).variance next * L /
            (stage.observations s a).length) +
            c₂ * cap * L / (stage.observations s a).length) := by ring
  · have hz : (stage.observations s a).length = 0 := Nat.eq_zero_of_not_pos hN
    rw [onlineCappedStageQ_zero_count cap L c₁ c₂ stage next s a hz]
    simp only [onlineRegretAnalysisCharge, hN, ↓reduceDIte]
    have hr := stage.environment.reward_nonneg s a
    have hm := (onlineObservedPlanningRow stage s a).expectation_nonneg hnext
    linarith

/-- One greedy capped-backup step along an arbitrary realized successor.
The two fluctuations are left as explicit algebraic terms; in particular, the
empirical term is not assumed centered or independent. -/
theorem onlineCappedStage_greedy_step_telescope
    (cap L c₁ c₂ : ℝ) (stage : OnlineObservedPlanningStage State Action)
    (tail : List (OnlineObservedPlanningStage State Action))
    (s sNext : State) (a : Action)
    (hcap : 0 ≤ cap) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hAction : Nonempty Action)
    (hgreedy : onlineCappedStageQ cap L c₁ c₂ stage
        (onlineCappedBackwardValue cap L c₁ c₂ tail) s a =
      actionMaximum (onlineCappedStageQ cap L c₁ c₂ stage
        (onlineCappedBackwardValue cap L c₁ c₂ tail) s)) :
    onlineCappedBackwardValue cap L c₁ c₂ (stage :: tail) s ≤
      stage.environment.reward s a +
        onlineRegretAnalysisCharge cap L c₁ c₂ stage
          (onlineCappedBackwardValue cap L c₁ c₂ tail) s a +
        ((onlineObservedPlanningRow stage s a).expectation
            (onlineCappedBackwardValue cap L c₁ c₂ tail) -
          (stage.environment.transition s a).expectation
            (onlineCappedBackwardValue cap L c₁ c₂ tail)) +
        ((stage.environment.transition s a).expectation
            (onlineCappedBackwardValue cap L c₁ c₂ tail) -
          onlineCappedBackwardValue cap L c₁ c₂ tail sNext) +
        onlineCappedBackwardValue cap L c₁ c₂ tail sNext := by
  have hnext : ∀ x, 0 ≤ onlineCappedBackwardValue cap L c₁ c₂ tail x := by
    exact fun x => (onlineCappedBackwardValue_range cap L c₁ c₂
      hcap hL hc₁ hc₂ tail x).1
  have hbackup := onlineCappedStageQ_le_analysisBackup cap L c₁ c₂ stage
    (onlineCappedBackwardValue cap L c₁ c₂ tail) hnext s a
  letI : Nonempty Action := hAction
  change actionMaximum
      (onlineCappedStageQ cap L c₁ c₂ stage
        (onlineCappedBackwardValue cap L c₁ c₂ tail) s) ≤ _
  rw [← hgreedy]
  calc
    onlineCappedStageQ cap L c₁ c₂ stage
        (onlineCappedBackwardValue cap L c₁ c₂ tail) s a ≤
      stage.environment.reward s a +
        (onlineObservedPlanningRow stage s a).expectation
          (onlineCappedBackwardValue cap L c₁ c₂ tail) +
        onlineRegretAnalysisCharge cap L c₁ c₂ stage
          (onlineCappedBackwardValue cap L c₁ c₂ tail) s a := hbackup
    _ = stage.environment.reward s a +
        onlineRegretAnalysisCharge cap L c₁ c₂ stage
          (onlineCappedBackwardValue cap L c₁ c₂ tail) s a +
        ((onlineObservedPlanningRow stage s a).expectation
            (onlineCappedBackwardValue cap L c₁ c₂ tail) -
          (stage.environment.transition s a).expectation
            (onlineCappedBackwardValue cap L c₁ c₂ tail)) +
        ((stage.environment.transition s a).expectation
            (onlineCappedBackwardValue cap L c₁ c₂ tail) -
          onlineCappedBackwardValue cap L c₁ c₂ tail sNext) +
        onlineCappedBackwardValue cap L c₁ c₂ tail sNext := by ring

/-- Pure finite telescoping principle used to unroll the preceding source
step. It makes no probabilistic or independence claim. -/
theorem onlineRealSequence_telescope_from
    (H m : ℕ) (v g : ℕ → ℝ)
    (hstep : ∀ n, v n ≤ g n + v (n + 1)) :
    v m ≤ (∑ n ∈ Finset.range H, g (m + n)) + v (m + H) := by
  induction H generalizing m with
  | zero => simp
  | succ H ih =>
      have hfirst := hstep m
      have htail := ih (m + 1)
      have hsum : (∑ n ∈ Finset.range (H + 1), g (m + n)) =
          g m + (∑ n ∈ Finset.range H, g (m + 1 + n)) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.add_zero]
        have hshift : (∑ n ∈ Finset.range H, g (m + (n + 1))) =
            (∑ n ∈ Finset.range H, g (m + (1 + n))) := by
          apply Finset.sum_congr rfl
          intro n hn
          congr 1
          omega
        rw [hshift]
        ring_nf
      calc
        v m ≤ g m + v (m + 1) := hfirst
        _ ≤ g m + ((∑ n ∈ Finset.range H, g (m + 1 + n)) + v (m + 1 + H)) :=
          by linarith [htail]
        _ = (∑ n ∈ Finset.range (H + 1), g (m + n)) + v (m + (H + 1)) := by
          rw [hsum]
          have hidx : m + 1 + H = m + (H + 1) := by omega
          rw [hidx]
          ring

/-- Episode telescope for a stage-indexed capped table and any path whose
selected action maximizes the corresponding source Q row. `stage` is the
pre-episode observed table; `state` and `action` describe one realized path.
The proof is deterministic and does not require that the path be likely. -/
theorem onlineCappedEpisode_realized_telescope
    (H : ℕ) (stage : Fin H → OnlineObservedPlanningStage State Action)
    (state : ℕ → State) (action : ℕ → Action)
    (δ' c₁ c₂ : ℝ) (hδ' : 0 < δ') (hδ'small : δ' ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁ ^ 2 ≤ c₂)
    (hAction : ∀ h : Fin H, Nonempty Action)
    (hgreedy : ∀ h : Fin H,
      letI : Nonempty Action := hAction h
      onlineCappedStageQ (H : ℝ) (Real.log (1 / δ')) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1))) (state h.val) (action h.val) =
      actionMaximum (onlineCappedStageQ (H : ℝ) (Real.log (1 / δ')) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1))) (state h.val))) :
    onlineCappedEpisodeValueAlongPath stage state (H : ℝ) (Real.log (1 / δ')) c₁ c₂ 0 ≤
      ∑ n ∈ Finset.range H,
        onlineCappedEpisodeTelescopeSummand H stage state action (Real.log (1 / δ')) c₁ c₂ n := by
  let stages := List.ofFn stage
  have hL : 0 ≤ Real.log (1 / δ') := by
    have hlog := onlineSmallConfidence_log_ge_one δ' hδ' hδ'small
    linarith
  have hc₁' : 0 ≤ c₁ := by linarith
  have hc₂' : 0 ≤ c₂ := by nlinarith [hc₁]
  let v : ℕ → ℝ := fun n =>
    onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
      (stages.drop n) (state n)
  let g : ℕ → ℝ := fun n =>
    onlineCappedEpisodeTelescopeSummand H stage state action (Real.log (1 / δ')) c₁ c₂ n
  have hstep : ∀ n, v n ≤ g n + v (n + 1) := by
    intro n
    by_cases hn : n < H
    · let h : Fin H := ⟨n, hn⟩
      have hdrop : stages.drop n = stage h :: stages.drop (n + 1) := by
        have hi : n < stages.length := by simpa [stages] using hn
        simpa only [stages, List.getElem_ofFn] using List.drop_eq_getElem_cons hi
      have hnext : ∀ x, 0 ≤ onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          (stages.drop (n + 1)) x := by
        exact fun x => (onlineCappedBackwardValue_range (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          (by positivity) hL hc₁' hc₂'  (stages.drop (n + 1)) x).1
      have hrow := onlineCappedStage_greedy_step_telescope (H : ℝ) (Real.log (1 / δ')) c₁ c₂
        (stage h) (stages.drop (n + 1)) (state n) (state (n + 1)) (action n)
        (by positivity) hL hc₁' hc₂' (hAction h) (hgreedy h)
      have hcurrent : v n =
          onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
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

/-- Generic corrected optimism-to-four-terms consumer. All fluctuation arrays
are arbitrary real data: this is deterministic algebra and asserts no
mean-zero, independence, concentration, or bonus-envelope property. -/
theorem onlineRegret_le_T1_T2_T3_T4
    (H K : ℕ) (initial : Fin K → State)
    (optimal estimate policyValue : Fin K → State → ℝ)
    (reward analysisCharge empiricalError transitionNoise : Fin K → Fin H → ℝ)
    (hoptimism : ∀ k, optimal k (initial k) ≤ estimate k (initial k))
    (htelescope : ∀ k,
      estimate k (initial k) ≤ ∑ h : Fin H,
        (reward k h + analysisCharge k h + empiricalError k h + transitionNoise k h)) :
    ∑ k : Fin K, (optimal k (initial k) - policyValue k (initial k)) ≤
      (∑ k : Fin K, ∑ h : Fin H, empiricalError k h) +
      (∑ k : Fin K, ∑ h : Fin H, analysisCharge k h) +
      (∑ k : Fin K, ∑ h : Fin H, transitionNoise k h) +
      (∑ k : Fin K,
        ((∑ h : Fin H, reward k h) - policyValue k (initial k))) := by
  have hEpisode : ∀ k : Fin K,
      optimal k (initial k) - policyValue k (initial k) ≤
        (∑ h : Fin H, empiricalError k h) +
        (∑ h : Fin H, analysisCharge k h) +
        (∑ h : Fin H, transitionNoise k h) +
        ((∑ h : Fin H, reward k h) - policyValue k (initial k)) := by
    intro k
    have hsum : (∑ h : Fin H,
        (reward k h + analysisCharge k h + empiricalError k h + transitionNoise k h)) =
        (∑ h : Fin H, reward k h) + (∑ h : Fin H, analysisCharge k h) +
        (∑ h : Fin H, empiricalError k h) + (∑ h : Fin H, transitionNoise k h) := by
      simp only [Finset.sum_add_distrib]
    calc
      optimal k (initial k) - policyValue k (initial k) ≤
          estimate k (initial k) - policyValue k (initial k) :=
        sub_le_sub_right (hoptimism k) _
      _ ≤ (∑ h : Fin H,
          (reward k h + analysisCharge k h + empiricalError k h + transitionNoise k h)) -
          policyValue k (initial k) := sub_le_sub_right (htelescope k) _
      _ = _ := by rw [hsum]; ring
  calc
    _ ≤ ∑ k : Fin K,
        ((∑ h : Fin H, empiricalError k h) +
          (∑ h : Fin H, analysisCharge k h) +
          (∑ h : Fin H, transitionNoise k h) +
          ((∑ h : Fin H, reward k h) - policyValue k (initial k))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hEpisode k
    _ = _ := by simp only [Finset.sum_add_distrib]

/-- Actual action-prefix consumer: at every stage of a realized episode, the
action recorded by the sequential history maximizes the same capped Q table
that was computed from the completed-episode prefix. This is pathwise and
uses the production row-consistency/action-prefix and pre-episode planner
exports; it makes no claim about probabilities of histories. -/
theorem onlineSequentialEpisode_action_max
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) (h : Fin H)
    (L c₁ c₂ : ℝ) (hAction : Nonempty Action) :
    let planner := onlineCappedGreedyPlanner E L c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner)
      (K * H) [] path
    let prehist := history.take (k.val * H)
    let j := k.val * H + h.val
    onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
        (onlinePreEpisodePlanningStages E prehist k.val) h.val
        (onlineEpisodicCurrentState H K initial fallback
          (history.take j)) (history.get ⟨j, by
            have hlen := onlineSequentialPathHistory_length
              (onlineEpisodicChoose H K hH initial fallback planner)
              (K * H) [] path
            rw [hlen]
            have hk : k.val < K := k.isLt
            have hh : h.val < H := h.isLt
            have hlocal : k.val * H + h.val < (k.val + 1) * H := by
              rw [Nat.add_mul]
              omega
            have houter : (k.val + 1) * H ≤ K * H :=
              Nat.mul_le_mul_right H (Nat.succ_le_of_lt hk)
            omega⟩).1.2.2 =
      actionMaximum (onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
        (onlinePreEpisodePlanningStages E prehist k.val) h.val
        (onlineEpisodicCurrentState H K initial fallback
          (history.take j))) := by
  classical
  dsimp only
  letI : Nonempty Action := hAction
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner)
    (K * H) [] path
  let j := k.val * H + h.val
  have hlen : history.length = K * H := by
    simp [history, onlineSequentialPathHistory_length]
  have hj : j < history.length := by
    rw [hlen]
    have hk : k.val < K := k.isLt
    have hh : h.val < H := h.isLt
    have hlocal : k.val * H + h.val < (k.val + 1) * H := by
      rw [Nat.add_mul]
      omega
    have houter : (k.val + 1) * H ≤ K * H :=
      Nat.mul_le_mul_right H (Nat.succ_le_of_lt hk)
    omega
  have hdiv : j / H = k.val := by
    dsimp [j]
    rw [Nat.add_div_eq_of_add_mod_lt]
    · simp [Nat.mul_div_cancel_left, hH, Nat.div_eq_of_lt h.isLt]
    · simp [Nat.mul_mod_right, Nat.mod_eq_of_lt h.isLt]
  have hmod : j % H = h.val := by
    dsimp [j]
    rw [Nat.add_mod_of_add_mod_lt]
    · simp [Nat.mul_mod_right, Nat.mod_eq_of_lt h.isLt]
    · simp [Nat.mul_mod_right, Nat.mod_eq_of_lt h.isLt]
  have hbound : k.val * H ≤ history.length := by
    rw [hlen]
    exact Nat.mul_le_mul_right H k.isLt.le
  have hprefixlen : (history.take (k.val * H)).length = k.val * H := by
    simp [Nat.min_eq_left hbound]
  have hselected := onlineSequential_actualAction_completedPrefix
    H K hH E initial fallback planner path
  have hselectedAt := hselected ⟨j, hj⟩
  have hselected' : (history.get ⟨j, hj⟩).1.2.2 =
      planner (history.take (k.val * H)) h
        (onlineEpisodicCurrentState H K initial fallback
          (history.take j)) := by
    simpa [history, j, hdiv, hmod] using hselectedAt
  have hmax := onlineCappedGreedyPlanner_preEpisode_max E L c₁ c₂
    (history.take (k.val * H)) k.val hprefixlen h
    (onlineEpisodicCurrentState H K initial fallback
      (history.take j))
  rw [hselected']
  exact hmax

/-- The same action-maximality fact in the head-recursion form consumed by the
episode backup telescope. -/
theorem onlineSequentialEpisode_backup_is_greedy
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) (h : Fin H)
    (L c₁ c₂ : ℝ) (hAction : Nonempty Action) :
    let planner := onlineCappedGreedyPlanner E L c₁ c₂
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner)
      (K * H) [] path
    let prehist := history.take (k.val * H)
    let stages := onlinePreEpisodePlanningStages E prehist k.val
    onlineCappedStageQ (H : ℝ) L c₁ c₂
        (onlineHistoryPlanningStage E prehist h)
        (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ (stages.drop (h.val + 1)))
        (onlineEpisodicCurrentState H K initial fallback
          (history.take (k.val * H + h.val)))
        (history.get ⟨k.val * H + h.val, by
          have hlen := onlineSequentialPathHistory_length
            (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
          rw [hlen]
          have hk : k.val < K := k.isLt
          have hh : h.val < H := h.isLt
          have hlocal : k.val * H + h.val < (k.val + 1) * H := by
            rw [Nat.add_mul]
            omega
          have houter : (k.val + 1) * H ≤ K * H :=
            Nat.mul_le_mul_right H (Nat.succ_le_of_lt hk)
          omega⟩).1.2.2 =
      actionMaximum (onlineCappedStageQ (H : ℝ) L c₁ c₂
        (onlineHistoryPlanningStage E prehist h)
        (onlineCappedBackwardValue (H : ℝ) L c₁ c₂ (stages.drop (h.val + 1)))
        (onlineEpisodicCurrentState H K initial fallback
          (history.take (k.val * H + h.val)))) := by
  classical
  dsimp only
  letI : Nonempty Action := hAction
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner)
    (K * H) [] path
  let prehist := history.take (k.val * H)
  let stages := onlinePreEpisodePlanningStages E prehist k.val
  have hpre : prehist.take (k.val * H) = prehist := by
    simp [prehist]
  have hmax := onlineSequentialEpisode_action_max H K hH E initial fallback
    path k h L c₁ c₂ hAction
  have hdrop := onlinePreEpisodePlanningStages_drop_stage E prehist k.val h
  rw [hpre] at hdrop
  change onlineCappedBackwardQAt (H : ℝ) L c₁ c₂ stages h.val
      (onlineEpisodicCurrentState H K initial fallback
        (history.take (k.val * H + h.val)))
      (history.get ⟨k.val * H + h.val, by
        have hlen := onlineSequentialPathHistory_length
          (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
        rw [hlen]
        have hk : k.val < K := k.isLt
        have hh : h.val < H := h.isLt
        have hlocal : k.val * H + h.val < (k.val + 1) * H := by
          rw [Nat.add_mul]
          omega
        have houter : (k.val + 1) * H ≤ K * H :=
          Nat.mul_le_mul_right H (Nat.succ_le_of_lt hk)
        omega⟩).1.2.2 = _ at hmax
  rw [onlineCappedBackwardQAt, hdrop] at hmax
  simpa [prehist, history, stages, onlineCappedBackwardQ] using hmax

/-- The observed row at episode `k`, stage `h` is exactly the row selected by
the causal planner from the completed episode prefix. This exposes the actual
state, greedy action and stage tag used by the deterministic telescope. -/
theorem onlineSequentialEpisode_actual_row
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) (h : Fin H) :
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    (history.get ⟨k.val * H + h.val, by
      have hlen := onlineSequentialPathHistory_length
        (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
      rw [hlen]
      simp only [List.length_nil, zero_add]
      calc
        k.val * H + h.val < k.val * H + H := Nat.add_lt_add_left h.isLt _
        _ = (k.val + 1) * H := by rw [Nat.succ_mul]
        _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1 =
      (h, (onlineEpisodicCurrentState H K initial fallback
        (history.take (k.val * H + h.val)),
        planner (history.take (k.val * H)) h
          (onlineEpisodicCurrentState H K initial fallback
            (history.take (k.val * H + h.val))))) := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let actualHistory := onlineSequentialPathHistory choose (K * H) [] path
  change (actualHistory.get ⟨k.val * H + h.val, by
      have hlen := onlineSequentialPathHistory_length choose (K * H) [] path
      rw [hlen]
      simp only [List.length_nil, zero_add]
      calc
        k.val * H + h.val < k.val * H + H := Nat.add_lt_add_left h.isLt _
        _ = (k.val + 1) * H := by rw [Nat.succ_mul]
        _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).1 =
      (h, (onlineEpisodicCurrentState H K initial fallback
        (actualHistory.take (k.val * H + h.val)),
        planner (actualHistory.take (k.val * H)) h
          (onlineEpisodicCurrentState H K initial fallback
            (actualHistory.take (k.val * H + h.val)))))
  let j := k.val * H + h.val
  have hj : j < actualHistory.length := by
    have hlen := onlineSequentialPathHistory_length choose (K * H) [] path
    rw [hlen]
    simp only [List.length_nil, zero_add]
    calc
      k.val * H + h.val < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  have hrows := onlineSequentialPathHistory_rows_consistent choose (K * H) []
    (by intro i; exact Fin.elim0 i) path
  have hrow := hrows ⟨j, hj⟩
  have htake : (actualHistory.take j).length = j := by
    simp only [List.length_take, Nat.min_eq_left hj.le]
  have hmod : j % H = h.val := by
    dsimp [j]
    calc
      (k.val * H + h.val) % H =
          ((k.val * H) % H + h.val % H) % H := by rw [Nat.add_mod]
      _ = h.val := by simp [Nat.mul_comm, Nat.mod_eq_of_lt h.isLt]
  have hdiv : j / H = k.val := by
    dsimp [j]
    calc
      (k.val * H + h.val) / H = (h.val + k.val * H) / H := by rw [Nat.add_comm]
      _ = h.val / H + k.val := Nat.add_mul_div_right _ _ hH
      _ = k.val := by simp [Nat.div_eq_of_lt h.isLt]
  have hcompleted : (j / H) * H = k.val * H := by rw [hdiv]
  have hle : k.val * H ≤ j := by
    dsimp [j]
    exact Nat.le_add_right _ _
  have hprefix : (actualHistory.take j).take ((j / H) * H) =
      actualHistory.take (k.val * H) := by
    rw [hcompleted, List.take_take, Nat.min_eq_left hle]
  change (actualHistory.get ⟨j, hj⟩).1 = choose (actualHistory.take j) at hrow
  rw [hrow]
  simp only [choose, onlineEpisodicChoose, htake]
  rw [hprefix]
  simp [j, hmod]

/-- The sequential current-state selector advances to the most recently
recorded successor whenever the new prefix is not an episode boundary. This
is the exact state bridge needed between adjacent backup stages; the boundary
case is the separate next-episode reset. -/
theorem onlineEpisodicCurrentState_after_observation
    (H K : ℕ) (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (history : List (OnlineMDPRow State Action H × State)) (j : ℕ)
    (hj : j < history.length) (hboundary : (j + 1) % H ≠ 0) :
    onlineEpisodicCurrentState H K initial fallback (history.take (j + 1)) =
      (history.get ⟨j, hj⟩).2 := by
  rw [← List.take_concat_get' history j hj]
  simp only [onlineEpisodicCurrentState]
  rw [List.getLast?_append_of_ne_nil _ (by simp)]
  simp [hboundary, List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hj)]

/-- At every nonterminal stage of a realized episode, the next selector state
is exactly the successor stored in the current row. The terminal stage is
handled separately because its continuation value is zero. -/
theorem onlineSequentialEpisode_successor_state
    (H K : ℕ) (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K) (h : Fin H)
    (hnext : h.val + 1 < H) :
    let history := onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
    onlineEpisodicCurrentState H K initial fallback
      (history.take (k.val * H + (h.val + 1))) =
      (history.get ⟨k.val * H + h.val, by
        have hlen := onlineSequentialPathHistory_length
          (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
        rw [hlen]
        simp only [List.length_nil, zero_add]
        calc
          k.val * H + h.val < k.val * H + H := Nat.add_lt_add_left h.isLt _
          _ = (k.val + 1) * H := by rw [Nat.succ_mul]
          _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)⟩).2 := by
  classical
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let history := onlineSequentialPathHistory choose (K * H) [] path
  let j := k.val * H + h.val
  have hj : j < history.length := by
    have hlen := onlineSequentialPathHistory_length choose (K * H) [] path
    rw [hlen]
    simp only [List.length_nil, zero_add]
    calc
      k.val * H + h.val < k.val * H + H := Nat.add_lt_add_left h.isLt _
      _ = (k.val + 1) * H := by rw [Nat.succ_mul]
      _ ≤ K * H := Nat.mul_le_mul_right H (Nat.succ_le_of_lt k.isLt)
  have hmod : j % H = h.val := by
    dsimp [j]
    calc
      (k.val * H + h.val) % H =
          ((k.val * H) % H + h.val % H) % H := by rw [Nat.add_mod]
      _ = h.val := by simp [Nat.mul_comm, Nat.mod_eq_of_lt h.isLt]
  have hone : 1 % H = 1 := Nat.mod_eq_of_lt (by omega)
  have hboundary : (j + 1) % H ≠ 0 := by
    have hmodNext : (j + 1) % H = h.val + 1 := by
      dsimp [j]
      calc
        (k.val * H + h.val + 1) % H =
            ((k.val * H + h.val) % H + 1 % H) % H := by rw [Nat.add_mod]
        _ = h.val + 1 := by rw [hmod, hone, Nat.mod_eq_of_lt hnext]
    rw [hmodNext]
    omega
  have hstate := onlineEpisodicCurrentState_after_observation H K hH initial
    fallback history j hj hboundary
  simpa [j, Nat.add_assoc, Nat.add_comm h.val 1] using hstate

/-- Deterministic telescope for one realized episode of the causal capped
planner. The pre-episode table and every row/action are extracted from the
same sequential history. No event or concentration premise is used. -/
theorem onlineSequentialEpisode_realized_telescope
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K)
    (δ' c₁ c₂ : ℝ) (hδ' : 0 < δ') (hδ'small : δ' ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁ ^ 2 ≤ c₂) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
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
    onlineCappedEpisodeValueAlongPath stage state (H : ℝ) (Real.log (1 / δ')) c₁ c₂ 0 ≤
      ∑ n ∈ Finset.range H,
        onlineCappedEpisodeTelescopeSummand H stage state action
          (Real.log (1 / δ')) c₁ c₂ n := by
  classical
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
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
      onlineCappedStageQ (H : ℝ) (Real.log (1 / δ')) c₁ c₂ (stage h)
        (onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1)))
        (state h.val) (action h.val) =
      actionMaximum (onlineCappedStageQ (H : ℝ) (Real.log (1 / δ')) c₁ c₂
        (stage h) (onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          ((List.ofFn stage).drop (h.val + 1))) (state h.val)) := by
    intro h
    letI : Nonempty Action := (E h).action_nonempty
    have hprefixlen := onlineSequential_episodePrefix_length H K hH E initial
      fallback planner path k.val k.isLt.le
    have hpre : prehist.take (k.val * H) = prehist := by
      rw [← hprefixlen, List.take_length]
    have hmax := onlineSequentialEpisode_backup_is_greedy H K hH E initial fallback
      path k h (Real.log (1 / δ')) c₁ c₂ (E h).action_nonempty
    have hmax' := hmax
    simp only [onlinePreEpisodePlanningStages] at hmax'
    rw [hpre] at hmax'
    simpa [planner, history, prehist, stages, stage, state, action, h.isLt] using hmax'
  simpa [planner, history, prehist, stages, stage, state, action] using
    onlineCappedEpisode_realized_telescope H stage state action δ' c₁ c₂
      hδ' hδ'small hc₁ hc₂ (fun h => (E h).action_nonempty) hgreedy

/-- Pathwise source-shaped regret decomposition for one episode, conditional
on the actual-history optimism event. The four terms are the empirical-row
error, corrected analysis bonus, transition sampling fluctuation, and the
realized reward sum minus the selected policy's actual finite-trajectory
value. The first term is not asserted to be centered. -/
theorem onlineSequentialEpisode_regret_decomposition
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (path : OnlineOutcomePath State (K * H)) (k : Fin K)
    (δ' c₁ c₂ : ℝ) (hδ' : 0 < δ') (hδ'small : δ' ≤ 1 / 100)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁ ^ 2 ≤ c₂)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ' c₁ c₂
      (onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂))
        (K * H) [] path)) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
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
    DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
        (initial k) - onlineCappedEpisodePolicyValue H hH E history k.val
          (initial k) (Real.log (1 / δ')) c₁ c₂ ≤
      (∑ n ∈ Finset.range H,
        onlineCappedEpisodeT1 H stage state action (Real.log (1 / δ')) c₁ c₂ n) +
      (∑ n ∈ Finset.range H,
        onlineCappedEpisodeT2 H stage state action (Real.log (1 / δ')) c₁ c₂ n) +
      (∑ n ∈ Finset.range H,
        onlineCappedEpisodeT3 H stage state action (Real.log (1 / δ')) c₁ c₂ n) +
      ((∑ n ∈ Finset.range H, onlineCappedEpisodeReward H E state action n) -
        onlineCappedEpisodePolicyValue H hH E history k.val
          (initial k) (Real.log (1 / δ')) c₁ c₂) := by
  classical
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
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
  have hprefixlen : prehist.length = k.val * H := by
    change (history.take (k.val * H)).length = k.val * H
    exact onlineSequential_episodePrefix_length H K hH E initial fallback planner path
      k.val k.isLt.le
  have hpre : prehist.take (k.val * H) = prehist := by
    rw [← hprefixlen, List.take_length]
  have hstate0 : state 0 = initial k := by
    dsimp [state]
    simpa using onlineEpisodicCurrentState_reset H K hH initial fallback
      prehist k hprefixlen
  have hopt := (hoptimism k ⟨0, hH⟩).1 (initial k)
  have hstage : onlinePreEpisodePlanningStages E history k.val = List.ofFn stage := by
    change List.ofFn (fun h => onlineHistoryPlanningStage E
      (history.take (k.val * H)) h) =
      List.ofFn (fun h => onlineHistoryPlanningStage E prehist h)
    rfl
  have hoptimisticEstimate :
      DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
          (initial k) ≤
        onlineCappedEpisodeValueAlongPath stage state (H : ℝ)
          (Real.log (1 / δ')) c₁ c₂ 0 := by
    change DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
        (initial k) ≤ onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ')) c₁ c₂
          (List.ofFn stage) (state 0)
    rw [hstate0, ← hstage]
    simpa [planner, history, stage, prehist, onlineCappedBackwardValueAt,
      onlinePreEpisodePlanningStages] using hopt
  have htelescope := onlineSequentialEpisode_realized_telescope H K hH E initial
    fallback path k δ' c₁ c₂ hδ' hδ'small hc₁ hc₂
  have hsum :
      (∑ n ∈ Finset.range H,
        onlineCappedEpisodeTelescopeSummand H stage state action
          (Real.log (1 / δ')) c₁ c₂ n) =
      (∑ n ∈ Finset.range H,
        onlineCappedEpisodeT1 H stage state action (Real.log (1 / δ')) c₁ c₂ n) +
      (∑ n ∈ Finset.range H,
        onlineCappedEpisodeT2 H stage state action (Real.log (1 / δ')) c₁ c₂ n) +
      (∑ n ∈ Finset.range H,
        onlineCappedEpisodeT3 H stage state action (Real.log (1 / δ')) c₁ c₂ n) +
      (∑ n ∈ Finset.range H, onlineCappedEpisodeReward H E state action n) := by
    calc
      _ = ∑ n ∈ Finset.range H,
          (onlineCappedEpisodeT1 H stage state action (Real.log (1 / δ')) c₁ c₂ n +
            onlineCappedEpisodeT2 H stage state action (Real.log (1 / δ')) c₁ c₂ n +
            onlineCappedEpisodeT3 H stage state action (Real.log (1 / δ')) c₁ c₂ n +
            onlineCappedEpisodeReward H E state action n) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnH : n < H := Finset.mem_range.mp hn
        simp [onlineCappedEpisodeTelescopeSummand, onlineCappedEpisodeT1,
          onlineCappedEpisodeT2, onlineCappedEpisodeT3,
          onlineCappedEpisodeReward, stage, onlineHistoryPlanningStage, hnH] <;> ring_nf
      _ = _ := by simp only [Finset.sum_add_distrib]
  have htelescope' : onlineCappedEpisodeValueAlongPath stage state (H : ℝ)
      (Real.log (1 / δ')) c₁ c₂ 0 ≤
      ∑ n ∈ Finset.range H,
        onlineCappedEpisodeTelescopeSummand H stage state action
          (Real.log (1 / δ')) c₁ c₂ n := by
    simpa [planner, history, prehist, stages, stage, state, action] using htelescope
  calc
    _ ≤ onlineCappedEpisodeValueAlongPath stage state (H : ℝ)
        (Real.log (1 / δ')) c₁ c₂ 0 -
          onlineCappedEpisodePolicyValue H hH E history k.val (initial k)
            (Real.log (1 / δ')) c₁ c₂ := sub_le_sub_right hoptimisticEstimate _
    _ ≤ (∑ n ∈ Finset.range H,
          onlineCappedEpisodeTelescopeSummand H stage state action
            (Real.log (1 / δ')) c₁ c₂ n) -
          onlineCappedEpisodePolicyValue H hH E history k.val (initial k)
            (Real.log (1 / δ')) c₁ c₂ := sub_le_sub_right htelescope' _
    _ = _ := by rw [hsum]; ring


/-!
The episode-level consumer composes the reset/current-state and
successor-index identities for `onlineSequentialPathHistory` with the
all-stage trajectory-optimism event at the episode's reset state. It proves a
pathwise decomposition conditional on that event. It does not bound T₁–T₄,
provide concentration, or establish a regret rate. T₁ remains data dependent,
as emphasized by the source's later W₁/W₂ split.
-/

end StatisticalRL.OnlineRL

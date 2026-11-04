import Formalization.Online.Regret.W1.OnlineW1PolicyVarianceBridge

/-! Actual continuation order and squared-gap variance bound for W₂. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w2GapStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w2GapActionDecidable : DecidableEq Action := Classical.decEq Action

/-- On actual optimism, the adaptive optimistic-minus-optimal gap lies in
[0,H] and is bounded by optimistic-minus-policy; this includes the terminal
suffix. The signs of bonus inputs are required by the actual capped recursion. -/
theorem onlineActualW2_gap_order
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hL : 0 ≤ Real.log (1 / δ)) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hoptimism : onlineHistoryAllStageTrajectoryOptimism H K E δ c₁ c₂
      (onlineSequentialPathHistory
        (onlineEpisodicChoose H K hH initial fallback
          (onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂))
        (K * H) [] path)) (h : Fin H) (k : Fin K) (s : State) :
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
    let V := onlineTrueSuffixRowFamily E (h, sa)
    let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
    0 ≤ U s - V s ∧ U s - V s ≤ U s - P s ∧ U s - P s ≤ H := by
  classical
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ)) c₁ c₂
  let history := onlineSequentialPathHistory
    (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let sa := onlineActualStageRowSequence H K hH initial fallback planner path h k.val
  let V := onlineTrueSuffixRowFamily E (h, sa)
  let P := onlineActualPolicyContinuation H K hH E initial fallback path δ c₁ c₂ h k
  let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ h k
  have hPV : P s ≤ V s := by
    let π := onlineCappedEpisodePolicy H hH E history k.val (Real.log (1 / δ)) c₁ c₂
    let a : Action := Classical.choice ((E h).action_nonempty)
    have hd := (EnvironmentStage.greedy_suffix_dominates (List.ofFn E) π (h.val + 1) s a).1
    simpa [P, V, π, onlineActualPolicyContinuation, onlineTrueSuffixRowFamily, history, planner,
      EnvironmentStage.greedy_suffix_value] using hd
  have hVU : V s ≤ U s := by
    by_cases hn : h.val + 1 < H
    · let next : Fin H := ⟨h.val + 1, hn⟩
      have ho := (hoptimism k next).1 s
      simpa [V, U, next, onlineTrueSuffixRowFamily, onlineActualOptimisticContinuation,
        history, planner, EnvironmentStage.greedy_suffix_value] using ho
    · have he : H ≤ h.val + 1 := by omega
      have htrue : (List.ofFn E).drop (h.val + 1) = [] := by
        apply List.drop_eq_nil_of_le
        simpa using he
      have hobs : (onlinePreEpisodePlanningStages E history k.val).drop (h.val + 1) = [] := by
        apply List.drop_eq_nil_of_le
        simpa [onlinePreEpisodePlanningStages] using he
      change EnvironmentStage.optimalValue ((List.ofFn E).drop (h.val + 1)) s ≤
        onlineCappedBackwardValue (H : ℝ) (Real.log (1 / δ)) c₁ c₂
          ((onlinePreEpisodePlanningStages E history k.val).drop (h.val + 1)) s
      rw [htrue, hobs]
      rfl
  have hP0 : 0 ≤ P s := by
    dsimp [P, onlineActualPolicyContinuation]
    rw [DecisionStage.trajectoryValue_eq_backwardValue]
    exact DecisionStage.backwardValue_nonneg _ s
  have hUH : U s ≤ H := by
    dsimp [U, onlineActualOptimisticContinuation, onlineCappedBackwardValueAt]
    exact (onlineCappedBackwardValue_range H (Real.log (1 / δ)) c₁ c₂
      (by exact_mod_cast Nat.zero_le H) hL hc₁ hc₂ _ s).2
  change 0 ≤ U s - V s ∧ U s - V s ≤ U s - P s ∧ U s - P s ≤ H
  constructor <;> [linarith; constructor <;> linarith]
end StatisticalRL.OnlineRL

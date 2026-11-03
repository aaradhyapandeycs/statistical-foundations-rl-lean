import Formalization.MDP.OptimalTrajectoryValue

/-!
# Exact discounted policy iteration

Source: arXiv:2610.41903v1, Chapter 2, `eq:policy_iteration` and its linear
convergence lemma. Each iteration greedily improves the Q value of the
preceding stationary policy, using the actual discounted model.
-/

open Filter
open scoped Topology

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- A chosen maximizer of an arbitrary action-value function. -/
noncomputable def greedyActionFor (M : DiscountedMDP State Action)
    (Q : State → Action → ℝ) (s : State) : Action := by
  letI : Nonempty Action := M.action_nonempty
  exact Classical.choose (EnvironmentStage.exists_maximizer (Q s))

theorem greedyActionFor_max (M : DiscountedMDP State Action)
    (Q : State → Action → ℝ) (s : State) :
    Q s (M.greedyActionFor Q s) =
      letI : Nonempty Action := M.action_nonempty
      actionMaximum (Q s) := by
  letI : Nonempty Action := M.action_nonempty
  exact Classical.choose_spec (EnvironmentStage.exists_maximizer (Q s))

/-- The source greedy policy update, represented by point-mass action laws. -/
noncomputable def greedyImprove (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : StationaryPolicy State Action :=
  fun s ↦ EnvironmentStage.pointMass (M.greedyActionFor (M.policyFixedPoint π) s)

/-- A greedy policy backup equals the optimality backup at the current Q. -/
theorem qBellman_greedyImprove (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    M.qBellman (M.greedyImprove π) (M.policyFixedPoint π) =
      M.qOptimality (M.policyFixedPoint π) := by
  letI : Nonempty Action := M.action_nonempty
  funext s a
  change M.reward s a + M.discount * (M.transition s a).expectation
      (fun t ↦ (EnvironmentStage.pointMass (M.greedyActionFor (M.policyFixedPoint π) t)).expectation
        (M.policyFixedPoint π t)) =
    M.reward s a + M.discount * (M.transition s a).expectation
      (fun t ↦ actionMaximum (M.policyFixedPoint π t))
  simp_rw [EnvironmentStage.expectation_pointMass, M.greedyActionFor_max]

/-- Every policy backup is bounded above by the maximum-action backup. -/
theorem qBellman_le_qOptimality (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (Q : State → Action → ℝ) :
    M.qBellman π Q ≤ M.qOptimality Q := by
  letI : Nonempty Action := M.action_nonempty
  intro s a
  change M.reward s a + M.discount * (M.transition s a).expectation
      (fun t ↦ (π t).expectation (Q t)) ≤
    M.reward s a + M.discount * (M.transition s a).expectation
      (fun t ↦ actionMaximum (Q t))
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ M.discount_nonneg
  apply (M.transition s a).expectation_mono
  intro t
  exact (π t).expectation_le_const (fun b ↦ le_actionMaximum _ b)

/-- One greedy policy-improvement step cannot decrease any policy Q-value. -/
theorem greedyImprove_policyFixedPoint_ge (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    M.policyFixedPoint π s a ≤ M.policyFixedPoint (M.greedyImprove π) s a := by
  have hstep : M.policyFixedPoint π ≤ M.qBellman (M.greedyImprove π) (M.policyFixedPoint π) := by
    calc
      M.policyFixedPoint π = M.qBellman π (M.policyFixedPoint π) :=
        (M.policyFixedPoint_spec π).symm
      _ ≤ M.qOptimality (M.policyFixedPoint π) := M.qBellman_le_qOptimality π _
      _ = M.qBellman (M.greedyImprove π) (M.policyFixedPoint π) :=
        (M.qBellman_greedyImprove π).symm
  have hiter : ∀ n : ℕ, M.policyFixedPoint π ≤
      (M.qBellman (M.greedyImprove π))^[n] (M.policyFixedPoint π) := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hstep.trans (M.qBellman_monotone (M.greedyImprove π) ih)
  have hlim := (tendsto_pi_nhds.mp
    ((tendsto_pi_nhds.mp (M.tendsto_policy_evaluation_iteration (M.greedyImprove π)
      (M.policyFixedPoint π))) s)) a
  exact ge_of_tendsto' hlim (fun n ↦ hiter n s a)

/-- The improved fixed point dominates a single optimality backup of the old one. -/
theorem qOptimality_policyFixedPoint_le_improved (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    M.qOptimality (M.policyFixedPoint π) ≤ M.policyFixedPoint (M.greedyImprove π) := by
  rw [← M.qBellman_greedyImprove, ← M.policyFixedPoint_spec (M.greedyImprove π)]
  exact M.qBellman_monotone _ (fun s a ↦ M.greedyImprove_policyFixedPoint_ge π s a)

/-- One policy-improvement step contracts the optimal Q error by γ. -/
theorem greedyImprove_error (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    ‖M.policyFixedPoint (M.greedyImprove π) - M.optimalityFixedPoint‖ ≤
      M.discount * ‖M.policyFixedPoint π - M.optimalityFixedPoint‖ := by
  have hbase : ‖M.optimalityFixedPoint - M.policyFixedPoint (M.greedyImprove π)‖ ≤
      ‖M.qOptimality M.optimalityFixedPoint - M.qOptimality (M.policyFixedPoint π)‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro s
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro a
    rw [Real.norm_eq_abs]
    have hnonneg : 0 ≤ M.optimalityFixedPoint s a -
        M.policyFixedPoint (M.greedyImprove π) s a :=
      sub_nonneg.mpr (M.policyFixedPoint_le_optimal _ s a)
    change |M.optimalityFixedPoint s a - M.policyFixedPoint (M.greedyImprove π) s a| ≤ _
    rw [abs_of_nonneg hnonneg]
    calc
      M.optimalityFixedPoint s a - M.policyFixedPoint (M.greedyImprove π) s a ≤
          M.qOptimality M.optimalityFixedPoint s a - M.qOptimality (M.policyFixedPoint π) s a := by
        rw [M.optimalityFixedPoint_spec]
        exact sub_le_sub_left (M.qOptimality_policyFixedPoint_le_improved π s a) _
      _ ≤ |M.qOptimality M.optimalityFixedPoint s a - M.qOptimality (M.policyFixedPoint π) s a| :=
        le_abs_self _
      _ ≤ ‖M.qOptimality M.optimalityFixedPoint - M.qOptimality (M.policyFixedPoint π)‖ := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using
          (norm_le_pi_norm ((M.qOptimality M.optimalityFixedPoint -
            M.qOptimality (M.policyFixedPoint π)) s) a).trans
          (norm_le_pi_norm (M.qOptimality M.optimalityFixedPoint -
            M.qOptimality (M.policyFixedPoint π)) s)
  have hcontract := M.norm_qOptimality_sub_le M.optimalityFixedPoint (M.policyFixedPoint π)
  simpa only [norm_sub_rev] using hbase.trans hcontract


/-- Every maximizing selector yields the same optimality backup, including
when different selectors resolve ties differently. -/
theorem qBellman_pointMass_of_maximizer (M : DiscountedMDP State Action)
    (Q : State → Action → ℝ) (f : State → Action)
    (hmax : letI : Nonempty Action := M.action_nonempty
      ∀ s, Q s (f s) = actionMaximum (Q s)) :
    M.qBellman (fun s ↦ EnvironmentStage.pointMass (f s)) Q = M.qOptimality Q := by
  letI : Nonempty Action := M.action_nonempty
  funext s a
  change M.reward s a + M.discount * (M.transition s a).expectation
      (fun t ↦ (EnvironmentStage.pointMass (f t)).expectation (Q t)) =
    M.reward s a + M.discount * (M.transition s a).expectation
      (fun t ↦ actionMaximum (Q t))
  simp_rw [EnvironmentStage.expectation_pointMass, hmax]

/-- A policy satisfying the greedy backup equality improves its predecessor. -/
theorem policyFixedPoint_le_of_greedy_backup (M : DiscountedMDP State Action)
    (π π' : StationaryPolicy State Action)
    (hgreedy : M.qBellman π' (M.policyFixedPoint π) = M.qOptimality (M.policyFixedPoint π)) :
    M.policyFixedPoint π ≤ M.policyFixedPoint π' := by
  have hstep : M.policyFixedPoint π ≤ M.qBellman π' (M.policyFixedPoint π) := by
    calc
      M.policyFixedPoint π = M.qBellman π (M.policyFixedPoint π) := (M.policyFixedPoint_spec π).symm
      _ ≤ M.qOptimality (M.policyFixedPoint π) := M.qBellman_le_qOptimality π _
      _ = M.qBellman π' (M.policyFixedPoint π) := hgreedy.symm
  have hiter : ∀ n : ℕ, M.policyFixedPoint π ≤ (M.qBellman π')^[n] (M.policyFixedPoint π) := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hstep.trans (M.qBellman_monotone π' ih)
  intro s a
  have hlim := (tendsto_pi_nhds.mp
    ((tendsto_pi_nhds.mp (M.tendsto_policy_evaluation_iteration π' (M.policyFixedPoint π))) s)) a
  exact ge_of_tendsto' hlim (fun n ↦ hiter n s a)

/-- The one-step rate holds for any exact greedy backup, not only for one
tie-breaking rule. -/
theorem policy_error_of_greedy_backup (M : DiscountedMDP State Action)
    (π π' : StationaryPolicy State Action)
    (hgreedy : M.qBellman π' (M.policyFixedPoint π) = M.qOptimality (M.policyFixedPoint π)) :
    ‖M.policyFixedPoint π' - M.optimalityFixedPoint‖ ≤
      M.discount * ‖M.policyFixedPoint π - M.optimalityFixedPoint‖ := by
  have hbackup : M.qOptimality (M.policyFixedPoint π) ≤ M.policyFixedPoint π' := by
    rw [← hgreedy, ← M.policyFixedPoint_spec π']
    exact M.qBellman_monotone _ (M.policyFixedPoint_le_of_greedy_backup π π' hgreedy)
  have hbase : ‖M.optimalityFixedPoint - M.policyFixedPoint π'‖ ≤
      ‖M.qOptimality M.optimalityFixedPoint - M.qOptimality (M.policyFixedPoint π)‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro s
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro a
    rw [Real.norm_eq_abs]
    have hnonneg : 0 ≤ M.optimalityFixedPoint s a - M.policyFixedPoint π' s a :=
      sub_nonneg.mpr (M.policyFixedPoint_le_optimal π' s a)
    change |M.optimalityFixedPoint s a - M.policyFixedPoint π' s a| ≤ _
    rw [abs_of_nonneg hnonneg]
    calc
      M.optimalityFixedPoint s a - M.policyFixedPoint π' s a ≤
          M.qOptimality M.optimalityFixedPoint s a - M.qOptimality (M.policyFixedPoint π) s a := by
        rw [M.optimalityFixedPoint_spec]
        exact sub_le_sub_left (hbackup s a) _
      _ ≤ |M.qOptimality M.optimalityFixedPoint s a - M.qOptimality (M.policyFixedPoint π) s a| :=
        le_abs_self _
      _ ≤ ‖M.qOptimality M.optimalityFixedPoint - M.qOptimality (M.policyFixedPoint π)‖ := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using
          (norm_le_pi_norm ((M.qOptimality M.optimalityFixedPoint -
            M.qOptimality (M.policyFixedPoint π)) s) a).trans
          (norm_le_pi_norm (M.qOptimality M.optimalityFixedPoint -
            M.qOptimality (M.policyFixedPoint π)) s)
  have hcontract := M.norm_qOptimality_sub_le M.optimalityFixedPoint (M.policyFixedPoint π)
  simpa only [norm_sub_rev] using hbase.trans hcontract

/-- The source PI rate holds for every sequence that selects an arbitrary
maximizing action at every state and iteration; ties need not be resolved by a
fixed rule. -/
theorem arbitraryGreedyPolicyIteration_error (M : DiscountedMDP State Action)
    (π : ℕ → StationaryPolicy State Action) (f : ℕ → State → Action)
    (hupdate : ∀ n, π (n + 1) = fun s ↦ EnvironmentStage.pointMass (f n s))
    (hmax : letI : Nonempty Action := M.action_nonempty
      ∀ n s, M.policyFixedPoint (π n) s (f n s) = actionMaximum (M.policyFixedPoint (π n) s))
    (n : ℕ) :
    ‖M.policyFixedPoint (π n) - M.optimalityFixedPoint‖ ≤
      M.discount ^ n * ‖M.policyFixedPoint (π 0) - M.optimalityFixedPoint‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hg : M.qBellman (π (n + 1)) (M.policyFixedPoint (π n)) =
        M.qOptimality (M.policyFixedPoint (π n)) := by
      rw [hupdate]
      exact M.qBellman_pointMass_of_maximizer _ _ (hmax n)
    calc
      _ ≤ M.discount * ‖M.policyFixedPoint (π n) - M.optimalityFixedPoint‖ :=
        M.policy_error_of_greedy_backup _ _ hg
      _ ≤ M.discount * (M.discount ^ n * ‖M.policyFixedPoint (π 0) - M.optimalityFixedPoint‖) :=
        mul_le_mul_of_nonneg_left ih M.discount_nonneg
      _ = _ := by rw [pow_succ]; ring

/-- Even with varying tie choices, some finite iterate has the optimal
Q-value: after the first step only finitely many deterministic policy values
can occur, and the source error bound forces their limit to be Q*. -/
theorem arbitraryGreedyPolicyIteration_finite_optimal (M : DiscountedMDP State Action)
    (π : ℕ → StationaryPolicy State Action) (f : ℕ → State → Action)
    (hupdate : ∀ n, π (n + 1) = fun s ↦ EnvironmentStage.pointMass (f n s))
    (hmax : letI : Nonempty Action := M.action_nonempty
      ∀ n s, M.policyFixedPoint (π n) s (f n s) = actionMaximum (M.policyFixedPoint (π n) s)) :
    ∃ n : ℕ, M.policyFixedPoint (π n) = M.optimalityFixedPoint := by
  have hp : Tendsto (fun n : ℕ ↦ M.discount ^ n *
      ‖M.policyFixedPoint (π 0) - M.optimalityFixedPoint‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one M.discount_nonneg M.discount_lt_one).mul_const
        ‖M.policyFixedPoint (π 0) - M.optimalityFixedPoint‖
  have hn : Tendsto (fun n : ℕ ↦ ‖M.policyFixedPoint (π n) - M.optimalityFixedPoint‖)
      atTop (𝓝 0) := squeeze_zero (fun _ ↦ norm_nonneg _)
        (M.arbitraryGreedyPolicyIteration_error π f hupdate hmax) hp
  have hlim : Tendsto (fun n ↦ M.policyFixedPoint (π n)) atTop (𝓝 M.optimalityFixedPoint) :=
    (tendsto_iff_norm_sub_tendsto_zero).2 hn
  let qdet : (State → Action) → State → Action → ℝ := fun g ↦
    M.policyFixedPoint (fun s ↦ EnvironmentStage.pointMass (g s))
  have hfinite : (Set.range (fun n : ℕ ↦ M.policyFixedPoint (π (n + 1)))).Finite := by
    apply (Set.finite_range qdet).subset
    rintro Q ⟨n, rfl⟩
    refine ⟨f n, ?_⟩
    change M.policyFixedPoint (fun s ↦ EnvironmentStage.pointMass (f n s)) =
      M.policyFixedPoint (π (n + 1))
    rw [hupdate]
  have hshift : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ n) tendsto_id
  have hlim' : Tendsto (fun n : ℕ ↦ M.policyFixedPoint (π (n + 1))) atTop
      (𝓝 M.optimalityFixedPoint) := hlim.comp hshift
  have hmem : M.optimalityFixedPoint ∈ Set.range (fun n : ℕ ↦ M.policyFixedPoint (π (n + 1))) :=
    hfinite.isClosed.mem_of_tendsto hlim' (Filter.Eventually.of_forall (fun n ↦ ⟨n, rfl⟩))
  obtain ⟨n, hn⟩ := hmem
  exact ⟨n + 1, hn⟩

/-- The arbitrary-tie source PI estimate stated directly in terms of the
actual infinite trajectory Q-values and the actual optimal greedy Q-value. -/
theorem arbitraryGreedyTrajectoryPolicyIteration_error (M : DiscountedMDP State Action)
    (π : ℕ → StationaryPolicy State Action) (f : ℕ → State → Action)
    (hupdate : ∀ n, π (n + 1) = fun s ↦ EnvironmentStage.pointMass (f n s))
    (hmax : letI : Nonempty Action := M.action_nonempty
      ∀ n s, M.trajectoryExpectedQ (π n) s (f n s) =
        actionMaximum (M.trajectoryExpectedQ (π n) s))
    (n : ℕ) :
    ‖M.trajectoryExpectedQ (π n) - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
      M.discount ^ n *
        ‖M.trajectoryExpectedQ (π 0) - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ := by
  have hq (π' : StationaryPolicy State Action) : M.trajectoryExpectedQ π' = M.policyFixedPoint π' := by
    funext s a
    exact M.trajectoryExpectedQ_eq_policyFixedPoint π' s a
  have hmax' : letI : Nonempty Action := M.action_nonempty
      ∀ n s, M.policyFixedPoint (π n) s (f n s) = actionMaximum (M.policyFixedPoint (π n) s) := by
    intro j s
    simpa only [hq] using hmax j s
  simpa only [hq, M.policyFixedPoint_optimalGreedy] using
    M.arbitraryGreedyPolicyIteration_error π f hupdate hmax' n

/-- With arbitrary tie choices, an actual trajectory Q-value equals the
constructed optimal trajectory Q after finitely many greedy updates. -/
theorem arbitraryGreedyTrajectoryPolicyIteration_finite_optimal
    (M : DiscountedMDP State Action)
    (π : ℕ → StationaryPolicy State Action) (f : ℕ → State → Action)
    (hupdate : ∀ n, π (n + 1) = fun s ↦ EnvironmentStage.pointMass (f n s))
    (hmax : letI : Nonempty Action := M.action_nonempty
      ∀ n s, M.trajectoryExpectedQ (π n) s (f n s) =
        actionMaximum (M.trajectoryExpectedQ (π n) s)) :
    ∃ n : ℕ, M.trajectoryExpectedQ (π n) = M.trajectoryExpectedQ M.optimalGreedyPolicy := by
  have hq (π' : StationaryPolicy State Action) : M.trajectoryExpectedQ π' = M.policyFixedPoint π' := by
    funext s a
    exact M.trajectoryExpectedQ_eq_policyFixedPoint π' s a
  have hmax' : letI : Nonempty Action := M.action_nonempty
      ∀ n s, M.policyFixedPoint (π n) s (f n s) = actionMaximum (M.policyFixedPoint (π n) s) := by
    intro j s
    simpa only [hq] using hmax j s
  obtain ⟨n, hn⟩ := M.arbitraryGreedyPolicyIteration_finite_optimal π f hupdate hmax'
  refine ⟨n, ?_⟩
  simpa only [hq, M.policyFixedPoint_optimalGreedy] using hn

/-- Deterministic greedy updates starting from an arbitrary stationary policy. -/
noncomputable def policyIteration (M : DiscountedMDP State Action)
    (π₀ : StationaryPolicy State Action) : ℕ → StationaryPolicy State Action
  | 0 => π₀
  | n + 1 => M.greedyImprove (M.policyIteration π₀ n)

/-- Exact source linear-convergence estimate for all iterations, including 0. -/
theorem policyIteration_error (M : DiscountedMDP State Action)
    (π₀ : StationaryPolicy State Action) (n : ℕ) :
    ‖M.policyFixedPoint (M.policyIteration π₀ n) - M.optimalityFixedPoint‖ ≤
      M.discount ^ n * ‖M.policyFixedPoint π₀ - M.optimalityFixedPoint‖ := by
  induction n with
  | zero => simp [policyIteration]
  | succ n ih =>
    change ‖M.policyFixedPoint (M.greedyImprove (M.policyIteration π₀ n)) -
      M.optimalityFixedPoint‖ ≤ _
    calc
      _ ≤ M.discount * ‖M.policyFixedPoint (M.policyIteration π₀ n) - M.optimalityFixedPoint‖ :=
        M.greedyImprove_error _
      _ ≤ M.discount * (M.discount ^ n *
          ‖M.policyFixedPoint π₀ - M.optimalityFixedPoint‖) :=
        mul_le_mul_of_nonneg_left ih M.discount_nonneg
      _ = _ := by rw [pow_succ]; ring

/-- The bound is for actual forced-action trajectory Q-values, not merely
formal fixed points. -/
theorem trajectoryPolicyIteration_error (M : DiscountedMDP State Action)
    (π₀ : StationaryPolicy State Action) (n : ℕ) :
    ‖M.trajectoryExpectedQ (M.policyIteration π₀ n) - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
      M.discount ^ n *
        ‖M.trajectoryExpectedQ π₀ - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ := by
  have hq (π : StationaryPolicy State Action) : M.trajectoryExpectedQ π = M.policyFixedPoint π := by
    funext s a
    exact M.trajectoryExpectedQ_eq_policyFixedPoint π s a
  simpa only [hq, M.policyFixedPoint_optimalGreedy] using M.policyIteration_error π₀ n

/-- Policy-iteration values increase at every step. -/
theorem policyIteration_monotone (M : DiscountedMDP State Action)
    (π₀ : StationaryPolicy State Action) (n : ℕ) :
    M.policyFixedPoint (M.policyIteration π₀ n) ≤
      M.policyFixedPoint (M.policyIteration π₀ (n + 1)) := by
  intro s a
  exact M.greedyImprove_policyFixedPoint_ge (M.policyIteration π₀ n) s a

/-- The exact source convergence rate implies convergence of the policy
iteration Q-functions to the unique optimality fixed point. -/
theorem tendsto_policyIteration (M : DiscountedMDP State Action)
    (π₀ : StationaryPolicy State Action) :
    Tendsto (fun n ↦ M.policyFixedPoint (M.policyIteration π₀ n)) atTop
      (𝓝 M.optimalityFixedPoint) := by
  have hp : Tendsto (fun n : ℕ ↦ M.discount ^ n *
      ‖M.policyFixedPoint π₀ - M.optimalityFixedPoint‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one M.discount_nonneg M.discount_lt_one).mul_const
        ‖M.policyFixedPoint π₀ - M.optimalityFixedPoint‖
  have hn : Tendsto (fun n : ℕ ↦
      ‖M.policyFixedPoint (M.policyIteration π₀ n) - M.optimalityFixedPoint‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) (M.policyIteration_error π₀) hp
  exact (tendsto_iff_norm_sub_tendsto_zero).2 hn

/-- Because every iterate after the first is a deterministic policy, there
are finitely many possible evaluated Q-functions. Convergence to Q* therefore
attains Q* at a finite iteration, independently of maximizing-action ties. -/
theorem policyIteration_finite_optimal (M : DiscountedMDP State Action)
    (π₀ : StationaryPolicy State Action) :
    ∃ n : ℕ, M.policyFixedPoint (M.policyIteration π₀ n) = M.optimalityFixedPoint := by
  let qdet : (State → Action) → State → Action → ℝ := fun f ↦
    M.policyFixedPoint (fun s ↦ EnvironmentStage.pointMass (f s))
  have hfinite : (Set.range (fun n : ℕ ↦
      M.policyFixedPoint (M.policyIteration π₀ (n + 1)))).Finite := by
    apply (Set.finite_range qdet).subset
    rintro Q ⟨n, rfl⟩
    refine ⟨fun s ↦ M.greedyActionFor (M.policyFixedPoint (M.policyIteration π₀ n)) s, ?_⟩
    rfl
  have hshift : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ n) tendsto_id
  have hlim : Tendsto (fun n : ℕ ↦ M.policyFixedPoint (M.policyIteration π₀ (n + 1)))
      atTop (𝓝 M.optimalityFixedPoint) := (M.tendsto_policyIteration π₀).comp hshift
  have hmem : M.optimalityFixedPoint ∈ Set.range (fun n : ℕ ↦
      M.policyFixedPoint (M.policyIteration π₀ (n + 1))) :=
    hfinite.isClosed.mem_of_tendsto hlim (Filter.Eventually.of_forall (fun n ↦ ⟨n, rfl⟩))
  obtain ⟨n, hn⟩ := hmem
  exact ⟨n + 1, hn⟩

/-- Once the optimal Q-value is reached, subsequent policy iterates retain it. -/
theorem policyIteration_optimal_persists (M : DiscountedMDP State Action)
    (π₀ : StationaryPolicy State Action) (n : ℕ)
    (hn : M.policyFixedPoint (M.policyIteration π₀ n) = M.optimalityFixedPoint) :
    ∀ m ≥ n, M.policyFixedPoint (M.policyIteration π₀ m) = M.optimalityFixedPoint := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact hn
  | succ m hnm ih =>
    apply le_antisymm
    · exact fun s a ↦ M.policyFixedPoint_le_optimal _ s a
    · rw [← ih]
      exact M.policyIteration_monotone π₀ m

/-- The fixed deterministic tie choice agrees with the constructed optimal
greedy policy whenever the current policy already has optimal Q. -/
theorem greedyImprove_eq_optimalGreedy_of_qeq (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (h : M.policyFixedPoint π = M.optimalityFixedPoint) :
    M.greedyImprove π = M.optimalGreedyPolicy := by
  unfold greedyImprove optimalGreedyPolicy
  funext s
  have ha : M.greedyActionFor (M.policyFixedPoint π) s = M.optimalGreedyAction s := by
    rw [h]
    rfl
  rw [ha]

/-- The deterministic tie rule makes the policy itself eventually equal to
the constructed optimal greedy policy, not just optimal in value. -/
theorem policyIteration_eventually_optimalGreedy (M : DiscountedMDP State Action)
    (π₀ : StationaryPolicy State Action) :
    ∃ n : ℕ, ∀ m ≥ n, M.policyIteration π₀ m = M.optimalGreedyPolicy := by
  obtain ⟨n, hn⟩ := M.policyIteration_finite_optimal π₀
  refine ⟨n + 1, ?_⟩
  intro m hm
  cases m with
  | zero => omega
  | succ k =>
    have hk : n ≤ k := Nat.le_of_succ_le_succ hm
    change M.greedyImprove (M.policyIteration π₀ k) = M.optimalGreedyPolicy
    exact M.greedyImprove_eq_optimalGreedy_of_qeq _
      (M.policyIteration_optimal_persists π₀ n hn k hk)

end StatisticalRL.DiscountedMDP

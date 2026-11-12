import Formalization.MDP.OptimalTrajectoryValue
import Formalization.ModelFree.QLearningRobustBallCompact

/-! select actual robust optimizer rows from the
actual robust fixed points and reduce their shifted range to ordinary MDP
optimality bounds. The final statistical Q-learning bound remains separate. -/
namespace StatisticalRL.QLearning
open StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The unique actual upper robust fixed point. -/
noncomputable def qRobustPlusFixedPoint (M : DiscountedMDP State Action) (ρ b : ℝ)
    (hρ : 0 ≤ ρ) : State → Action → ℝ :=
  Classical.choose ((qRobustBellman_fixedPoints_exist_unique M ρ b hρ).1)

theorem qRobustPlusFixedPoint_spec (M : DiscountedMDP State Action) (ρ b : ℝ)
    (hρ : 0 ≤ ρ) :
    qRobustBellmanPlus M ρ b (qRobustPlusFixedPoint M ρ b hρ) =
      qRobustPlusFixedPoint M ρ b hρ :=
  (Classical.choose_spec ((qRobustBellman_fixedPoints_exist_unique M ρ b hρ).1)).1

/-- The unique actual lower robust fixed point. -/
noncomputable def qRobustMinusFixedPoint (M : DiscountedMDP State Action) (ρ b : ℝ)
    (hρ : 0 ≤ ρ) : State → Action → ℝ :=
  Classical.choose ((qRobustBellman_fixedPoints_exist_unique M ρ b hρ).2)

theorem qRobustMinusFixedPoint_spec (M : DiscountedMDP State Action) (ρ b : ℝ)
    (hρ : 0 ≤ ρ) :
    qRobustBellmanMinus M ρ b (qRobustMinusFixedPoint M ρ b hρ) =
      qRobustMinusFixedPoint M ρ b hρ :=
  (Classical.choose_spec ((qRobustBellman_fixedPoints_exist_unique M ρ b hρ).2)).1

/-- For each row, choose a real feasible maximizer of the continuation value
at the upper robust fixed point. -/
noncomputable def qRobustPlusOptimizer (M : DiscountedMDP State Action) (ρ b : ℝ)
    (hρ : 0 ≤ ρ) (s : State) (a : Action) : FiniteDistribution State :=
  Classical.choose ((qChiBall_extrema_attained (M.transition s a) ρ hρ
    (qLearningValue M (qRobustPlusFixedPoint M ρ b hρ))).1)

theorem qRobustPlusOptimizer_spec (M : DiscountedMDP State Action) (ρ b : ℝ)
    (hρ : 0 ≤ ρ) (s : State) (a : Action) :
    qRobustPlusOptimizer M ρ b hρ s a ∈ qChiBall (M.transition s a) ρ ∧
      ∀ q ∈ qChiBall (M.transition s a) ρ,
        q.expectation (qLearningValue M (qRobustPlusFixedPoint M ρ b hρ)) ≤
          (qRobustPlusOptimizer M ρ b hρ s a).expectation
            (qLearningValue M (qRobustPlusFixedPoint M ρ b hρ)) :=
  Classical.choose_spec ((qChiBall_extrema_attained (M.transition s a) ρ hρ
    (qLearningValue M (qRobustPlusFixedPoint M ρ b hρ))).1)

/-- For each row, choose a real feasible minimizer at the lower robust fixed
point. The infimum side is selected independently. -/
noncomputable def qRobustMinusOptimizer (M : DiscountedMDP State Action) (ρ b : ℝ)
    (hρ : 0 ≤ ρ) (s : State) (a : Action) : FiniteDistribution State :=
  Classical.choose ((qChiBall_extrema_attained (M.transition s a) ρ hρ
    (qLearningValue M (qRobustMinusFixedPoint M ρ b hρ))).2)

theorem qRobustMinusOptimizer_spec (M : DiscountedMDP State Action) (ρ b : ℝ)
    (hρ : 0 ≤ ρ) (s : State) (a : Action) :
    qRobustMinusOptimizer M ρ b hρ s a ∈ qChiBall (M.transition s a) ρ ∧
      ∀ q ∈ qChiBall (M.transition s a) ρ,
        (qRobustMinusOptimizer M ρ b hρ s a).expectation
            (qLearningValue M (qRobustMinusFixedPoint M ρ b hρ)) ≤
          q.expectation (qLearningValue M (qRobustMinusFixedPoint M ρ b hρ)) :=
  Classical.choose_spec ((qChiBall_extrema_attained (M.transition s a) ρ hρ
    (qLearningValue M (qRobustMinusFixedPoint M ρ b hρ))).2)

/-- The selected upper row expectation is exactly the robust supremum. -/
theorem qRobustPlusOptimizer_sup (M : DiscountedMDP State Action) (ρ b : ℝ)
    (hρ : 0 ≤ ρ) (s : State) (a : Action) :
    sSup (qRobustExpectations (M.transition s a) ρ
      (qLearningValue M (qRobustPlusFixedPoint M ρ b hρ))) =
      (qRobustPlusOptimizer M ρ b hρ s a).expectation
        (qLearningValue M (qRobustPlusFixedPoint M ρ b hρ)) := by
  let U := qRobustExpectations (M.transition s a) ρ
    (qLearningValue M (qRobustPlusFixedPoint M ρ b hρ))
  have hb := qRobustExpectations_bounds (M.transition s a) ρ
    (qLearningValue M (qRobustPlusFixedPoint M ρ b hρ))
  have hz : (qRobustPlusOptimizer M ρ b hρ s a).expectation
      (qLearningValue M (qRobustPlusFixedPoint M ρ b hρ)) ∈ U :=
    ⟨qRobustPlusOptimizer M ρ b hρ s a,
      (qRobustPlusOptimizer_spec M ρ b hρ s a).1, rfl⟩
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, hz⟩
    · rintro z ⟨q, hq, rfl⟩
      exact (qRobustPlusOptimizer_spec M ρ b hρ s a).2 q hq
  · exact le_csSup hb.1 hz

/-- The selected lower row expectation is exactly the robust infimum. -/
theorem qRobustMinusOptimizer_inf (M : DiscountedMDP State Action) (ρ b : ℝ)
    (hρ : 0 ≤ ρ) (s : State) (a : Action) :
    sInf (qRobustExpectations (M.transition s a) ρ
      (qLearningValue M (qRobustMinusFixedPoint M ρ b hρ))) =
      (qRobustMinusOptimizer M ρ b hρ s a).expectation
        (qLearningValue M (qRobustMinusFixedPoint M ρ b hρ)) := by
  let U := qRobustExpectations (M.transition s a) ρ
    (qLearningValue M (qRobustMinusFixedPoint M ρ b hρ))
  have hb := qRobustExpectations_bounds (M.transition s a) ρ
    (qLearningValue M (qRobustMinusFixedPoint M ρ b hρ))
  have hz : (qRobustMinusOptimizer M ρ b hρ s a).expectation
      (qLearningValue M (qRobustMinusFixedPoint M ρ b hρ)) ∈ U :=
    ⟨qRobustMinusOptimizer M ρ b hρ s a,
      (qRobustMinusOptimizer_spec M ρ b hρ s a).1, rfl⟩
  apply le_antisymm
  · exact csInf_le hb.2 hz
  · apply le_csInf
    · exact ⟨_, hz⟩
    · rintro z ⟨q, hq, rfl⟩
      exact (qRobustMinusOptimizer_spec M ρ b hρ s a).2 q hq

/-- Optimizer rows assemble into actual finite transition kernels. -/
noncomputable def qRobustPlusModel (M : DiscountedMDP State Action) (ρ b : ℝ)
    (hρ : 0 ≤ ρ) : DiscountedMDP State Action where
  state_nonempty := M.state_nonempty
  action_nonempty := M.action_nonempty
  transition := qRobustPlusOptimizer M ρ b hρ
  reward := M.reward
  reward_nonneg := M.reward_nonneg
  reward_le_one := M.reward_le_one
  discount := M.discount
  discount_nonneg := M.discount_nonneg
  discount_lt_one := M.discount_lt_one

noncomputable def qRobustMinusModel (M : DiscountedMDP State Action) (ρ b : ℝ)
    (hρ : 0 ≤ ρ) : DiscountedMDP State Action where
  state_nonempty := M.state_nonempty
  action_nonempty := M.action_nonempty
  transition := qRobustMinusOptimizer M ρ b hρ
  reward := M.reward
  reward_nonneg := M.reward_nonneg
  reward_le_one := M.reward_le_one
  discount := M.discount
  discount_nonneg := M.discount_nonneg
  discount_lt_one := M.discount_lt_one

/-- Finite action maxima commute with subtracting an action-independent
constant. -/
theorem qActionMaximum_sub_const [Nonempty Action] (f : Action → ℝ) (c : ℝ) :
    actionMaximum (fun a ↦ f a - c) = actionMaximum f - c := by
  obtain ⟨a, ha⟩ := EnvironmentStage.exists_maximizer f
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty (fun a ↦ f a - c)).2
    intro a _
    exact sub_le_sub_right (le_actionMaximum f a) c
  · have h := le_actionMaximum (fun a ↦ f a - c) a
    rw [ha] at h
    linarith

/-- Finite action maxima commute with adding an action-independent constant. -/
theorem qActionMaximum_add_const [Nonempty Action] (f : Action → ℝ) (c : ℝ) :
    actionMaximum (fun a ↦ f a + c) = actionMaximum f + c := by
  obtain ⟨a, ha⟩ := EnvironmentStage.exists_maximizer f
  apply le_antisymm
  · apply (Finset.sup'_le_iff Finset.univ_nonempty (fun a ↦ f a + c)).2
    intro a _
    simpa [add_comm] using add_le_add_right (le_actionMaximum f a) c
  · have h := le_actionMaximum (fun a ↦ f a + c) a
    rw [ha] at h
    linarith

/-- Each shifted robust fixed point is the ordinary optimality fixed point
for the kernel formed from its actual row optimizers. -/
theorem qRobustComparator_shifted_fixedPoints
    (M : DiscountedMDP State Action) (ρ b : ℝ) (hρ : 0 ≤ ρ) :
    (fun s a ↦ qRobustPlusFixedPoint M ρ b hρ s a - b / (1 - M.discount)) =
      (qRobustPlusModel M ρ b hρ).optimalityFixedPoint ∧
    (fun s a ↦ qRobustMinusFixedPoint M ρ b hρ s a + b / (1 - M.discount)) =
      (qRobustMinusModel M ρ b hρ).optimalityFixedPoint := by
  let c : ℝ := b / (1 - M.discount)
  have hden : 1 - M.discount ≠ 0 := ne_of_gt (sub_pos.mpr M.discount_lt_one)
  have hbc : b = (1 - M.discount) * c := by
    dsimp [c]
    field_simp
  letI : Nonempty Action := M.action_nonempty
  have hplusFixed :
      (qRobustPlusModel M ρ b hρ).qOptimality
        (fun s a ↦ qRobustPlusFixedPoint M ρ b hρ s a - c) =
      (fun s a ↦ qRobustPlusFixedPoint M ρ b hρ s a - c) := by
    funext s a
    have hfix := congrFun (congrFun (qRobustPlusFixedPoint_spec M ρ b hρ) s) a
    have hs := qRobustPlusOptimizer_sup M ρ b hρ s a
    change M.reward s a + b + M.discount *
      sSup (qRobustExpectations (M.transition s a) ρ
        (qLearningValue M (qRobustPlusFixedPoint M ρ b hρ))) =
      qRobustPlusFixedPoint M ρ b hρ s a at hfix
    rw [hs] at hfix
    change M.reward s a + b + M.discount *
      (qRobustPlusOptimizer M ρ b hρ s a).expectation
        (fun t ↦ actionMaximum (qRobustPlusFixedPoint M ρ b hρ t)) =
      qRobustPlusFixedPoint M ρ b hρ s a at hfix
    change M.reward s a + M.discount *
      (qRobustPlusOptimizer M ρ b hρ s a).expectation
        (fun t ↦ actionMaximum (fun a ↦ qRobustPlusFixedPoint M ρ b hρ t a - c)) =
      qRobustPlusFixedPoint M ρ b hρ s a - c
    have hmax (t : State) :
        actionMaximum (fun a ↦ qRobustPlusFixedPoint M ρ b hρ t a - c) =
          actionMaximum (fun a ↦ qRobustPlusFixedPoint M ρ b hρ t a) - c :=
      qActionMaximum_sub_const _ _
    simp_rw [hmax]
    simp only [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_const]
    have hbceq : b = c - M.discount * c := by nlinarith [hbc]
    linarith
  have hminusFixed :
      (qRobustMinusModel M ρ b hρ).qOptimality
        (fun s a ↦ qRobustMinusFixedPoint M ρ b hρ s a + c) =
      (fun s a ↦ qRobustMinusFixedPoint M ρ b hρ s a + c) := by
    funext s a
    have hfix := congrFun (congrFun (qRobustMinusFixedPoint_spec M ρ b hρ) s) a
    have hs := qRobustMinusOptimizer_inf M ρ b hρ s a
    change M.reward s a - b + M.discount *
      sInf (qRobustExpectations (M.transition s a) ρ
        (qLearningValue M (qRobustMinusFixedPoint M ρ b hρ))) =
      qRobustMinusFixedPoint M ρ b hρ s a at hfix
    rw [hs] at hfix
    change M.reward s a - b + M.discount *
      (qRobustMinusOptimizer M ρ b hρ s a).expectation
        (fun t ↦ actionMaximum (qRobustMinusFixedPoint M ρ b hρ t)) =
      qRobustMinusFixedPoint M ρ b hρ s a at hfix
    change M.reward s a + M.discount *
      (qRobustMinusOptimizer M ρ b hρ s a).expectation
        (fun t ↦ actionMaximum (fun a ↦ qRobustMinusFixedPoint M ρ b hρ t a + c)) =
      qRobustMinusFixedPoint M ρ b hρ s a + c
    have hmax (t : State) :
        actionMaximum (fun a ↦ qRobustMinusFixedPoint M ρ b hρ t a + c) =
          actionMaximum (fun a ↦ qRobustMinusFixedPoint M ρ b hρ t a) + c := by
      exact qActionMaximum_add_const
        (fun a ↦ qRobustMinusFixedPoint M ρ b hρ t a) c
    simp_rw [hmax]
    simp only [FiniteDistribution.expectation_add, FiniteDistribution.expectation_const]
    have hbceq : b = c - M.discount * c := by nlinarith [hbc]
    linarith
  exact ⟨((qRobustPlusModel M ρ b hρ).optimalityFixedPoint_characterization _).mp hplusFixed,
    ((qRobustMinusModel M ρ b hρ).optimalityFixedPoint_characterization _).mp hminusFixed⟩

/-- The selected robust fixed points have the source's shifted [0,H] range.
Their corresponding state-value functions therefore have span at most H. -/
theorem qRobustComparator_shifted_range
    (M : DiscountedMDP State Action) (ρ b : ℝ) (hρ : 0 ≤ ρ) :
    (∀ s a, 0 ≤ qRobustPlusFixedPoint M ρ b hρ s a - b / (1 - M.discount) ∧
      qRobustPlusFixedPoint M ρ b hρ s a - b / (1 - M.discount) ≤ M.effectiveHorizon) ∧
    (∀ s a, 0 ≤ qRobustMinusFixedPoint M ρ b hρ s a + b / (1 - M.discount) ∧
      qRobustMinusFixedPoint M ρ b hρ s a + b / (1 - M.discount) ≤ M.effectiveHorizon) := by
  obtain ⟨hplus, hminus⟩ := qRobustComparator_shifted_fixedPoints M ρ b hρ
  constructor
  · intro s a
    have hx := congrFun (congrFun hplus s) a
    rw [hx]
    exact (qRobustPlusModel M ρ b hρ).optimalityFixedPoint_bounds s a
  · intro s a
    have hx := congrFun (congrFun hminus s) a
    rw [hx]
    exact (qRobustMinusModel M ρ b hρ).optimalityFixedPoint_bounds s a

/-- The state-value comparators have span at most H, expressed as the
pairwise range bound needed for variance and centered-draw estimates. -/
theorem qRobustComparator_value_pairwise_span
    (M : DiscountedMDP State Action) (ρ b : ℝ) (hρ : 0 ≤ ρ)
    (s t : State) :
    |qLearningValue M (qRobustPlusFixedPoint M ρ b hρ) s -
        qLearningValue M (qRobustPlusFixedPoint M ρ b hρ) t| ≤ M.effectiveHorizon ∧
    |qLearningValue M (qRobustMinusFixedPoint M ρ b hρ) s -
        qLearningValue M (qRobustMinusFixedPoint M ρ b hρ) t| ≤ M.effectiveHorizon := by
  letI : Nonempty Action := M.action_nonempty
  have hrange := qRobustComparator_shifted_range M ρ b hρ
  have hplus (x : State) :
      0 ≤ qLearningValue M (qRobustPlusFixedPoint M ρ b hρ) x -
          b / (1 - M.discount) ∧
        qLearningValue M (qRobustPlusFixedPoint M ρ b hρ) x -
          b / (1 - M.discount) ≤ M.effectiveHorizon := by
    change 0 ≤ actionMaximum (qRobustPlusFixedPoint M ρ b hρ x) -
        b / (1 - M.discount) ∧
      actionMaximum (qRobustPlusFixedPoint M ρ b hρ x) -
        b / (1 - M.discount) ≤ M.effectiveHorizon
    rw [← qActionMaximum_sub_const]
    constructor
    · obtain ⟨a, ha⟩ := EnvironmentStage.exists_maximizer
        (fun a ↦ qRobustPlusFixedPoint M ρ b hρ x a - b / (1 - M.discount))
      rw [← ha]
      exact (hrange.1 x a).1
    · apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
      intro a _
      exact (hrange.1 x a).2
  have hminus (x : State) :
      0 ≤ qLearningValue M (qRobustMinusFixedPoint M ρ b hρ) x +
          b / (1 - M.discount) ∧
        qLearningValue M (qRobustMinusFixedPoint M ρ b hρ) x +
          b / (1 - M.discount) ≤ M.effectiveHorizon := by
    change 0 ≤ actionMaximum (qRobustMinusFixedPoint M ρ b hρ x) +
        b / (1 - M.discount) ∧
      actionMaximum (qRobustMinusFixedPoint M ρ b hρ x) +
        b / (1 - M.discount) ≤ M.effectiveHorizon
    rw [← qActionMaximum_add_const]
    constructor
    · obtain ⟨a, ha⟩ := EnvironmentStage.exists_maximizer
        (fun a ↦ qRobustMinusFixedPoint M ρ b hρ x a + b / (1 - M.discount))
      rw [← ha]
      exact (hrange.2 x a).1
    · apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
      intro a _
      exact (hrange.2 x a).2
  constructor
  · have hs := hplus s
    have ht := hplus t
    apply abs_le.mpr
    constructor <;> linarith
  · have hs := hminus s
    have ht := hminus t
    apply abs_le.mpr
    constructor <;> linarith

end StatisticalRL.QLearning

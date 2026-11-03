import Formalization.Obstructions.OneStateExperiment

/-!
# One-state policy-learning obstruction in the generative experiment

Use a deterministic least-index reward maximizer, measurable jointly in the
known reward table and the other observable inputs. The rule ignores samples.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.Obstructions

/-- The finite set of actions attaining the largest known reward. -/
noncomputable def rewardMaximizers (reward : SingletonState → SixteenActions → ℝ)
    (s : SingletonState) : Finset SixteenActions := by
  classical
  exact Finset.univ.filter (fun a ↦ reward s a = actionMaximum (reward s))

theorem rewardMaximizers_nonempty (reward : SingletonState → SixteenActions → ℝ)
    (s : SingletonState) : (rewardMaximizers reward s).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := EnvironmentStage.exists_maximizer (reward s)
  exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩

/-- Tie-break reward maxima by the least action index. -/
noncomputable def measurableRewardGreedy (reward : SingletonState → SixteenActions → ℝ)
    (s : SingletonState) : SixteenActions :=
  (rewardMaximizers reward s).min' (rewardMaximizers_nonempty reward s)

theorem measurableRewardGreedy_max (reward : SingletonState → SixteenActions → ℝ)
    (s : SingletonState) : reward s (measurableRewardGreedy reward s) = actionMaximum (reward s) := by
  classical
  have h := Finset.min'_mem (rewardMaximizers reward s) (rewardMaximizers_nonempty reward s)
  exact (Finset.mem_filter.mp h).2

theorem measurableRewardGreedy_eq_iff (reward : SingletonState → SixteenActions → ℝ)
    (s : SingletonState) (a : SixteenActions) :
    measurableRewardGreedy reward s = a ↔
      reward s a = actionMaximum (reward s) ∧
        ∀ b, reward s b = actionMaximum (reward s) → a ≤ b := by
  classical
  unfold measurableRewardGreedy
  rw [Finset.min'_eq_iff]
  simp only [rewardMaximizers, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The deterministic selector is Borel measurable as a function of rewards. -/
theorem measurableRewardGreedy_measurable (s : SingletonState) :
    Measurable (fun reward : SingletonState → SixteenActions → ℝ ↦
      measurableRewardGreedy reward s) := by
  apply measurable_to_countable'
  intro a
  have hr (b : SixteenActions) :
      Measurable (fun reward : SingletonState → SixteenActions → ℝ ↦ reward s b) :=
    (measurable_pi_apply b).comp (measurable_pi_apply s)
  have hm : Measurable (fun reward : SingletonState → SixteenActions → ℝ ↦
      actionMaximum (reward s)) := by
    unfold actionMaximum
    exact Finset.measurable_sup' Finset.univ_nonempty (fun b _ ↦ hr b)
  have heq (b : SixteenActions) : MeasurableSet {reward : SingletonState → SixteenActions → ℝ |
      reward s b = actionMaximum (reward s)} := measurableSet_eq_fun (hr b) hm
  have hless (b : SixteenActions) : MeasurableSet {reward : SingletonState → SixteenActions → ℝ |
      reward s b = actionMaximum (reward s) → a ≤ b} := by
    by_cases hab : a ≤ b
    · simpa only [hab, implies_true] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set (SingletonState → SixteenActions → ℝ)))
    · convert (heq b).compl using 1
      ext reward
      simp [hab]
  have hset : (fun reward : SingletonState → SixteenActions → ℝ ↦
      measurableRewardGreedy reward s) ⁻¹' {a} =
      {reward | reward s a = actionMaximum (reward s)} ∩
        ⋂ b : SixteenActions, {reward | reward s b = actionMaximum (reward s) → a ≤ b} := by
    ext reward
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_iInter, measurableRewardGreedy_eq_iff]
  rw [hset]
  exact (heq a).inter (MeasurableSet.iInter hless)

/-- One deterministic policy estimator, depending only on known reward. -/
noncomputable def oneStatePolicyEstimator (reward : SingletonState → SixteenActions → ℝ)
    (_discount : ℝ) (_data : OneSampleData) : SingletonState → SixteenActions :=
  measurableRewardGreedy reward

/-- The rule is jointly measurable in known rewards, discount and sample data. -/
theorem oneStatePolicyEstimator_joint_measurable :
    Measurable (fun input : (SingletonState → SixteenActions → ℝ) × ℝ × OneSampleData ↦
      oneStatePolicyEstimator input.1 input.2.1 input.2.2) := by
  apply measurable_pi_lambda
  intro s
  exact (measurableRewardGreedy_measurable s).comp measurable_fst

/-- On one-state MDPs the estimator attains the actual trajectory optimal Q. -/
theorem oneStatePolicyEstimator_actualQ (M : DiscountedMDP SingletonState SixteenActions)
    (data : OneSampleData) (s : SingletonState) (a : SixteenActions) :
    M.trajectoryExpectedQ
      (fun t ↦ EnvironmentStage.pointMass (oneStatePolicyEstimator M.reward M.discount data t)) s a =
      M.trajectoryExpectedQ M.optimalGreedyPolicy s a := by
  rw [M.trajectoryExpectedQ_eq_policyFixedPoint, oneState_trajectoryOptimalQ]
  have heq : M.policyFixedPoint
      (fun t ↦ EnvironmentStage.pointMass (oneStatePolicyEstimator M.reward M.discount data t)) =
      oneStateQ M := by
    symm
    apply (M.policyFixedPoint_characterization _ (oneStateQ M)).mp
    funext x b
    have hconst : (fun t ↦
        (EnvironmentStage.pointMass (oneStatePolicyEstimator M.reward M.discount data t)).expectation
          (oneStateQ M t)) =
        (fun _ ↦ (EnvironmentStage.pointMass (oneStatePolicyEstimator M.reward M.discount data x)).expectation
          (oneStateQ M x)) := by
      funext t
      rw [Subsingleton.elim t x]
    change M.reward x b + M.discount *
      (M.transition x b).expectation
        (fun t ↦ (EnvironmentStage.pointMass (oneStatePolicyEstimator M.reward M.discount data t)).expectation
          (oneStateQ M t)) = oneStateQ M x b
    rw [hconst, FiniteDistribution.expectation_const, EnvironmentStage.expectation_pointMass]
    unfold oneStateQ oneStatePolicyEstimator
    rw [measurableRewardGreedy_max M.reward x]
    have hne : 1 - M.discount ≠ 0 := ne_of_gt (sub_pos.mpr M.discount_lt_one)
    field_simp
    ring
  exact congrFun (congrFun heq s) a

/-- Zero full-array Q policy loss on every data outcome. -/
theorem oneStatePolicyEstimator_loss (M : DiscountedMDP SingletonState SixteenActions)
    (data : OneSampleData) :
    ‖(fun s a ↦ M.trajectoryExpectedQ
      (fun t ↦ EnvironmentStage.pointMass (oneStatePolicyEstimator M.reward M.discount data t)) s a) -
      (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖ = 0 := by
  have heq : (fun s a ↦ M.trajectoryExpectedQ
      (fun t ↦ EnvironmentStage.pointMass (oneStatePolicyEstimator M.reward M.discount data t)) s a) =
      (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a) := by
    funext s a
    exact oneStatePolicyEstimator_actualQ M data s a
  rw [heq, sub_self, norm_zero]

/-- Its strict Q-policy-loss event has probability zero under actual samples. -/
theorem oneStatePolicyEstimator_failure (M : DiscountedMDP SingletonState SixteenActions)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (oneStateGenerativeLaw M).real {data | ε < ‖(fun s a ↦ M.trajectoryExpectedQ
      (fun t ↦ EnvironmentStage.pointMass (oneStatePolicyEstimator M.reward M.discount data t)) s a) -
      (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖} = 0 := by
  have hempty : {data : OneSampleData | ε < ‖(fun s a ↦ M.trajectoryExpectedQ
      (fun t ↦ EnvironmentStage.pointMass (oneStatePolicyEstimator M.reward M.discount data t)) s a) -
      (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖} = ∅ := by
    ext data
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rw [oneStatePolicyEstimator_loss M data]
    exact not_lt_of_ge hε
  rw [hempty]
  simp [Measure.real]


/-- A single deterministic policy rule defeats the proposed lower bound for
all admissible one-state models, at feasible parameters for every c > 0. -/
theorem oneState_theorem37_i_obstruction (c : ℝ) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / (32 * (1 - (2 : ℝ) / 3)) ∧
      (2 : ℝ) / 3 ≤ 2 / 3 ∧ (2 : ℝ) / 3 < 1 ∧
      16 ≤ Fintype.card SingletonState * Fintype.card SixteenActions ∧
      1 ≤ c * Real.log 16 / ((1 - (2 : ℝ) / 3) ^ 3 * ε ^ 2) ∧
      (∃ M : DiscountedMDP SingletonState SixteenActions, M.discount = (2 : ℝ) / 3) ∧
      ∃ estimator : (SingletonState → SixteenActions → ℝ) → ℝ → OneSampleData →
          SingletonState → SixteenActions,
        Measurable (fun input : (SingletonState → SixteenActions → ℝ) × ℝ × OneSampleData ↦
          estimator input.1 input.2.1 input.2.2) ∧
        ∀ M : DiscountedMDP SingletonState SixteenActions,
          M.discount = (2 : ℝ) / 3 →
          (∀ data, ‖(fun s a ↦ M.trajectoryExpectedQ
            (fun t ↦ EnvironmentStage.pointMass (estimator M.reward M.discount data t)) s a) -
              (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖ = 0) ∧
          (oneStateGenerativeLaw M).real {data | ε < ‖(fun s a ↦ M.trajectoryExpectedQ
            (fun t ↦ EnvironmentStage.pointMass (estimator M.reward M.discount data t)) s a) -
              (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖} < 1 / 4 := by
  obtain ⟨ε, hε, hεup, hγlo, hγhi, hsize, hN⟩ :=
    oneState_theorem37_hypotheses_feasible c hc
  refine ⟨ε, hε, hεup, hγlo, hγhi, hsize, hN,
    ⟨oneStateExampleMDP, oneStateExampleMDP_discount⟩,
    oneStatePolicyEstimator, oneStatePolicyEstimator_joint_measurable, ?_⟩
  intro M hγ
  refine ⟨oneStatePolicyEstimator_loss M, ?_⟩
  rw [oneStatePolicyEstimator_failure M ε hε.le]
  norm_num

end StatisticalRL.Obstructions

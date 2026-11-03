import Formalization.Obstructions.OneStateTrajectory
import Formalization.Obstructions.OneStateParameters
import Formalization.Probability.EmpiricalRow

/-!
# One-state generative experiment and Q-estimation obstruction

A finite product of the actual row laws gives one independent transition
sample for every state-action row. The estimator is a single known-reward
rule, uniform in the unknown model and data.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.Obstructions

abbrev SingletonState := Fin 1
abbrev SixteenActions := Fin 16
abbrev OneSampleIndex := (SingletonState × SixteenActions) × Fin 1
abbrev OneSampleData := OneSampleIndex → SingletonState

local instance singletonStateMeasurable : MeasurableSpace SingletonState := ⊤

/-- Each coordinate is an actual sample from its associated MDP transition row. -/
noncomputable def oneStateGenerativeLaw (M : DiscountedMDP SingletonState SixteenActions) :
    Measure OneSampleData :=
  Measure.pi (fun i : OneSampleIndex ↦ (M.transition i.1.1 i.1.2).rowMeasure)

instance oneStateGenerativeLaw_probability (M : DiscountedMDP SingletonState SixteenActions) :
    IsProbabilityMeasure (oneStateGenerativeLaw M) := by
  unfold oneStateGenerativeLaw
  infer_instance

/-- Each state-action observation has exactly the required transition-row law. -/
theorem oneStateGenerativeLaw_marginal (M : DiscountedMDP SingletonState SixteenActions)
    (i : OneSampleIndex) :
    (oneStateGenerativeLaw M).map (fun data ↦ data i) =
      (M.transition i.1.1 i.1.2).rowMeasure := by
  exact (measurePreserving_eval (fun i : OneSampleIndex ↦
    (M.transition i.1.1 i.1.2).rowMeasure) i).map_eq

/-- The full indexed family of observations is jointly independent. -/
theorem oneStateGenerativeLaw_independent (M : DiscountedMDP SingletonState SixteenActions) :
    iIndepFun (fun i (data : OneSampleData) ↦ data i) (oneStateGenerativeLaw M) := by
  exact iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)

/-- A concrete admissible model witnesses that the fixed-size class is nonempty. -/
noncomputable def oneStateExampleMDP : DiscountedMDP SingletonState SixteenActions where
  state_nonempty := inferInstance
  action_nonempty := inferInstance
  transition := fun _ _ ↦ EnvironmentStage.pointMass 0
  reward := fun _ _ ↦ 0
  reward_nonneg := by intros; norm_num
  reward_le_one := by intros; norm_num
  discount := 2 / 3
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

/-- The model witness has the discount used in the counterexample. -/
theorem oneStateExampleMDP_discount : oneStateExampleMDP.discount = (2 : ℝ) / 3 := rfl

/-- The estimator accepts only observed known inputs and the generated data. -/
noncomputable def oneStateExperimentEstimator (reward : SingletonState → SixteenActions → ℝ)
    (discount : ℝ) (data : OneSampleData) : SingletonState → SixteenActions → ℝ :=
  oneStateKnownRewardEstimator reward discount data

/-- For each known reward and discount, this data-dependent estimator is measurable. -/
theorem oneStateExperimentEstimator_measurable
    (reward : SingletonState → SixteenActions → ℝ) (discount : ℝ) :
    Measurable (oneStateExperimentEstimator reward discount) := by
  exact measurable_const

/-- The single rule is jointly Borel measurable in the known reward,
discount and data, including the harmless total-division value at discount one. -/
theorem oneStateExperimentEstimator_joint_measurable :
    Measurable (fun input : (SingletonState → SixteenActions → ℝ) × ℝ × OneSampleData ↦
      oneStateExperimentEstimator input.1 input.2.1 input.2.2) := by
  apply measurable_pi_lambda
  intro s
  apply measurable_pi_lambda
  intro a
  have hr (s : SingletonState) (a : SixteenActions) :
      Measurable (fun input : (SingletonState → SixteenActions → ℝ) × ℝ × OneSampleData ↦
        input.1 s a) :=
    (measurable_pi_apply a).comp ((measurable_pi_apply s).comp measurable_fst)
  have hm (s : SingletonState) :
      Measurable (fun input : (SingletonState → SixteenActions → ℝ) × ℝ × OneSampleData ↦
        actionMaximum (input.1 s)) := by
    unfold actionMaximum
    exact Finset.measurable_sup' Finset.univ_nonempty (fun a _ ↦ hr s a)
  have hg : Measurable (fun input : (SingletonState → SixteenActions → ℝ) × ℝ × OneSampleData ↦
      input.2.1) := measurable_fst.comp measurable_snd
  change Measurable (fun input : (SingletonState → SixteenActions → ℝ) × ℝ × OneSampleData ↦
    input.1 s a + input.2.1 * actionMaximum (input.1 s) / (1 - input.2.1))
  exact (hr s a).add ((hg.mul (hm s)).div (measurable_const.sub hg))

/-- The estimator has zero strict-error probability for every admissible model. -/
theorem oneStateExperimentEstimator_failure (M : DiscountedMDP SingletonState SixteenActions)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (oneStateGenerativeLaw M).real {data |
      ε < ‖oneStateExperimentEstimator M.reward M.discount data -
        (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖} = 0 := by
  unfold oneStateExperimentEstimator Measure.real
  rw [oneStateKnownRewardEstimator_error_measure (oneStateGenerativeLaw M)
    M.reward M.discount M rfl rfl ε hε, ENNReal.toReal_zero]

/-- For any positive proposed universal constant, the printed parameter range
is feasible and a single estimator succeeds on every admissible model. -/
theorem oneState_theorem37_ii_obstruction (c : ℝ) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / (32 * (1 - (2 : ℝ) / 3)) ∧
      (2 : ℝ) / 3 ≤ 2 / 3 ∧ (2 : ℝ) / 3 < 1 ∧
      16 ≤ Fintype.card SingletonState * Fintype.card SixteenActions ∧
      1 ≤ c * Real.log 16 / ((1 - (2 : ℝ) / 3) ^ 3 * ε ^ 2) ∧
      (∃ M : DiscountedMDP SingletonState SixteenActions, M.discount = (2 : ℝ) / 3) ∧
      ∃ estimator : (SingletonState → SixteenActions → ℝ) → ℝ → OneSampleData →
          SingletonState → SixteenActions → ℝ,
        (∀ reward discount, Measurable (estimator reward discount)) ∧
        Measurable (fun input : (SingletonState → SixteenActions → ℝ) × ℝ × OneSampleData ↦
          estimator input.1 input.2.1 input.2.2) ∧
        ∀ M : DiscountedMDP SingletonState SixteenActions,
          M.discount = (2 : ℝ) / 3 →
          (oneStateGenerativeLaw M).real {data |
            ε < ‖estimator M.reward M.discount data -
              (fun s a ↦ M.trajectoryExpectedQ M.optimalGreedyPolicy s a)‖} < 1 / 4 := by
  obtain ⟨ε, hε, hεup, hγlo, hγhi, hsize, hN⟩ :=
    oneState_theorem37_hypotheses_feasible c hc
  refine ⟨ε, hε, hεup, hγlo, hγhi, hsize, hN, ⟨oneStateExampleMDP, oneStateExampleMDP_discount⟩,
    oneStateExperimentEstimator, ?_, ?_, ?_⟩
  · exact oneStateExperimentEstimator_measurable
  · exact oneStateExperimentEstimator_joint_measurable
  · intro M hγ
    rw [oneStateExperimentEstimator_failure M ε hε.le]
    norm_num

end StatisticalRL.Obstructions

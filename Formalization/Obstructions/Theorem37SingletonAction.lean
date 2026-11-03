import Formalization.MDP.OptimalTrajectoryValue
import Formalization.Obstructions.SingletonAction
import Formalization.Obstructions.OneStateParameters
import Formalization.Probability.EmpiricalRow
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Theorem 3.7(i) singleton-action obstruction (conditional source reading)

This module formalizes a counterexample to the theorem's literal displayed
domain at S=16 and A=1. The prior policy-learning section states A≥2; whether
that standing convention carries into the separate minimax-lower-bounds
section is unresolved. This is not an author-approved correction or a claim
about intended scope. The experiment uses N=1 independent draws from every
actual transition row, and loss is evaluated by the actual infinite-horizon
trajectory Q-function.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.Obstructions

abbrev C1State := Fin 16
abbrev C1Action := Fin 1
abbrev C1Index := (C1State × C1Action) × Fin 1
abbrev C1Data := C1Index → C1State

local instance c1StateMeasurable : MeasurableSpace C1State := ⊤
local instance c1ActionMeasurable : MeasurableSpace C1Action := ⊤

/-- Actual N=1 samples from every state-action transition row. -/
noncomputable def c1GenerativeLaw (M : DiscountedMDP C1State C1Action) : Measure C1Data :=
  Measure.pi (fun i : C1Index ↦ (M.transition i.1.1 i.1.2).rowMeasure)

instance c1GenerativeLaw_probability (M : DiscountedMDP C1State C1Action) :
    IsProbabilityMeasure (c1GenerativeLaw M) := by
  unfold c1GenerativeLaw
  infer_instance

theorem c1GenerativeLaw_marginal (M : DiscountedMDP C1State C1Action) (i : C1Index) :
    (c1GenerativeLaw M).map (fun data ↦ data i) =
      (M.transition i.1.1 i.1.2).rowMeasure := by
  exact (measurePreserving_eval
    (fun i : C1Index ↦ (M.transition i.1.1 i.1.2).rowMeasure) i).map_eq

theorem c1GenerativeLaw_independent (M : DiscountedMDP C1State C1Action) :
    iIndepFun (fun i (data : C1Data) ↦ data i) (c1GenerativeLaw M) := by
  exact iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)

/-- A deterministic, data-independent policy estimator choosing the only action. -/
def c1PolicyEstimator (_data : C1Data) : C1State → C1Action := fun _ ↦ 0

theorem c1PolicyEstimator_measurable : Measurable c1PolicyEstimator := measurable_const

/-- For every MDP, the estimated policy and the chosen optimal deterministic
policy are the same, so their actual forced-action trajectory Q-functions agree. -/
theorem c1PolicyEstimator_actualQ (M : DiscountedMDP C1State C1Action) (data : C1Data) :
    (fun s a ↦ M.trajectoryExpectedQ
      (fun t ↦ EnvironmentStage.pointMass (c1PolicyEstimator data t)) s a) =
      M.trajectoryExpectedQ M.optimalGreedyPolicy := by
  have hpolicy : c1PolicyEstimator data = M.optimalGreedyAction := by
    funext s
    exact Subsingleton.elim _ _
  rw [hpolicy]
  rfl

theorem c1PolicyEstimator_loss (M : DiscountedMDP C1State C1Action) (data : C1Data) :
    ‖(fun s a ↦ M.trajectoryExpectedQ
      (fun t ↦ EnvironmentStage.pointMass (c1PolicyEstimator data t)) s a) -
      M.trajectoryExpectedQ M.optimalGreedyPolicy‖ = 0 := by
  rw [c1PolicyEstimator_actualQ M data, sub_self, norm_zero]

theorem c1PolicyEstimator_failure (M : DiscountedMDP C1State C1Action) (ε : ℝ)
    (hε : 0 ≤ ε) :
    (c1GenerativeLaw M).real {data | ε < ‖(fun s a ↦ M.trajectoryExpectedQ
      (fun t ↦ EnvironmentStage.pointMass (c1PolicyEstimator data t)) s a) -
      M.trajectoryExpectedQ M.optimalGreedyPolicy‖} = 0 := by
  have hempty : {data : C1Data | ε < ‖(fun s a ↦ M.trajectoryExpectedQ
      (fun t ↦ EnvironmentStage.pointMass (c1PolicyEstimator data t)) s a) -
      M.trajectoryExpectedQ M.optimalGreedyPolicy‖} = ∅ := by
    ext data
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rw [c1PolicyEstimator_loss M data]
    exact not_lt_of_ge hε
  rw [hempty]
  simp [Measure.real]

/-- Parameter feasibility at the displayed SA=16 boundary. This packages only
the theorem's explicit numerical assumptions; interpretation of A=1 remains
conditional on reading its displayed quantifiers standalone. -/
theorem c1_displayed_parameters_feasible (c : ℝ) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / (32 * (1 - (2 : ℝ) / 3)) ∧
      (2 : ℝ) / 3 ≤ 2 / 3 ∧ (2 : ℝ) / 3 < 1 ∧
      16 ≤ Fintype.card C1State * Fintype.card C1Action ∧
      1 ≤ c * Real.log 16 / ((1 - (2 : ℝ) / 3) ^ 3 * ε ^ 2) := by
  obtain ⟨ε, hε, hεup, hbudget⟩ := oneState_parameter_feasible c hc
  exact ⟨ε, hε, hεup, by norm_num, by norm_num, by norm_num, hbudget⟩

/-- Conditional refutation of the literal standalone displayed domain: the
fixed estimator has zero failure probability for every admissible MDP. -/
theorem c1_literal_displayed_domain_obstruction (c : ℝ) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / (32 * (1 - (2 : ℝ) / 3)) ∧
      (2 : ℝ) / 3 ≤ 2 / 3 ∧ (2 : ℝ) / 3 < 1 ∧
      16 ≤ Fintype.card C1State * Fintype.card C1Action ∧
      1 ≤ c * Real.log 16 / ((1 - (2 : ℝ) / 3) ^ 3 * ε ^ 2) ∧
      ∃ estimator : C1Data → C1State → C1Action,
        Measurable estimator ∧
        ∀ M : DiscountedMDP C1State C1Action, M.discount = (2 : ℝ) / 3 →
          (c1GenerativeLaw M).real {data | ε < ‖(fun s a ↦ M.trajectoryExpectedQ
            (fun t ↦ EnvironmentStage.pointMass (estimator data t)) s a) -
            M.trajectoryExpectedQ M.optimalGreedyPolicy‖} < 1 / 4 := by
  obtain ⟨ε, hε, hεup, hγlo, hγhi, hsize, hbudget⟩ :=
    c1_displayed_parameters_feasible c hc
  refine ⟨ε, hε, hεup, hγlo, hγhi, hsize, hbudget,
    c1PolicyEstimator, c1PolicyEstimator_measurable, ?_⟩
  intro M hγ
  rw [c1PolicyEstimator_failure M ε hε.le]
  norm_num

end StatisticalRL.Obstructions

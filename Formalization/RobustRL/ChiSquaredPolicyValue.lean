import Formalization.MDP.OptimalTrajectoryValue
import Formalization.ModelFree.QLearningRobustComparator

/-!
# Robust χ² policy values for stationary randomized policies

The policy-specific robust value is the infimum of actual infinite discounted
trajectory values over complete kernels whose rows lie in the support-aware
χ² ball. The policy carrier in this module is `StationaryPolicy`; the benchmark
is a supremum over those stationary randomized policies. Attainment and the
zero-gap/failure-event results are proved only on a subsingleton action space.
This module does not prove general robust optimal-policy attainment or a
Theorem 7.5 lower bound. This is a quarantined production-layout preview.
-/

namespace StatisticalRL.RobustRL

open StatisticalRL.QLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

local instance robustChiPolicyValueStateMeasurable : MeasurableSpace State := ⊤
local instance robustChiPolicyValueActionMeasurable : MeasurableSpace Action := ⊤

/-- An RMDP with a nominal finite MDP and a positive χ² row radius. -/
structure ChiSquaredRMDP where
  nominal : DiscountedMDP State Action
  radius : ℝ
  radius_pos : 0 < radius

/-- A complete transition kernel lies in the source's rectangular χ²
uncertainty set exactly when every row lies in its support-aware χ² ball. -/
def chiSquaredAdmissibleKernel (R : ChiSquaredRMDP (State := State) (Action := Action))
    (K : State → Action → FiniteDistribution State) : Prop :=
  ∀ s a, K s a ∈ qChiBall (R.nominal.transition s a) R.radius

/-- Replace the nominal transition rows by one candidate adversarial kernel,
leaving the source reward and discount unchanged. -/
def chiSquaredAdversarialMDP (R : ChiSquaredRMDP (State := State) (Action := Action))
    (K : State → Action → FiniteDistribution State) : DiscountedMDP State Action where
  state_nonempty := R.nominal.state_nonempty
  action_nonempty := R.nominal.action_nonempty
  transition := K
  reward := R.nominal.reward
  reward_nonneg := R.nominal.reward_nonneg
  reward_le_one := R.nominal.reward_le_one
  discount := R.nominal.discount
  discount_nonneg := R.nominal.discount_nonneg
  discount_lt_one := R.nominal.discount_lt_one

/-- The values attainable by the actual policy trajectory under an admissible
complete adversarial transition kernel. -/
def chiSquaredPolicyValueCandidates
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (π : StationaryPolicy State Action) (s : State) : Set ℝ :=
  {v | ∃ K, chiSquaredAdmissibleKernel R K ∧
    v = (chiSquaredAdversarialMDP R K).trajectoryExpectedValue π s}

/-- Source robust policy value `inf_{P∈U^ρ(P⁰)} V^{π,P}(s)`, represented by
the infimum over actual trajectory values of all row-wise χ²-feasible kernels. -/
noncomputable def chiSquaredRobustPolicyValue
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (π : StationaryPolicy State Action) (s : State) : ℝ :=
  sInf (chiSquaredPolicyValueCandidates R π s)

/-- The nominal transition kernel is a member of the uncertainty set at its
positive radius; this also covers rows with zero-mass coordinates. -/
theorem chiSquaredAdmissibleKernel_nominal
    (R : ChiSquaredRMDP (State := State) (Action := Action)) :
    chiSquaredAdmissibleKernel R R.nominal.transition := by
  intro s a
  exact qChiBall_self (R.nominal.transition s a) R.radius R.radius_pos.le

/-- The candidate set is nonempty because it contains the nominal actual
trajectory value. -/
theorem chiSquaredPolicyValueCandidates_nonempty
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (π : StationaryPolicy State Action) (s : State) :
    (chiSquaredPolicyValueCandidates R π s).Nonempty := by
  refine ⟨(chiSquaredAdversarialMDP R R.nominal.transition).trajectoryExpectedValue π s, ?_⟩
  exact ⟨R.nominal.transition, chiSquaredAdmissibleKernel_nominal R, rfl⟩

/-- Every candidate robust policy value is the expected discounted reward of
an actual MDP trajectory, hence lies in the source geometric range. -/
theorem chiSquaredPolicyValueCandidates_bounds
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (π : StationaryPolicy State Action) (s : State) {v : ℝ}
    (hv : v ∈ chiSquaredPolicyValueCandidates R π s) :
    0 ≤ v ∧ v ≤ 1 / (1 - R.nominal.discount) := by
  rcases hv with ⟨K, hK, rfl⟩
  exact (chiSquaredAdversarialMDP R K).trajectoryExpectedValue_bounds π s

/-- The source χ² robust policy value is well-defined as a finite real in the
same reward-horizon range. This does not assert optimality over policies. -/
theorem chiSquaredRobustPolicyValue_bounds
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (π : StationaryPolicy State Action) (s : State) :
    0 ≤ chiSquaredRobustPolicyValue R π s ∧
      chiSquaredRobustPolicyValue R π s ≤ 1 / (1 - R.nominal.discount) := by
  have hnonempty := chiSquaredPolicyValueCandidates_nonempty R π s
  have hbelow : BddBelow (chiSquaredPolicyValueCandidates R π s) := by
    refine ⟨0, ?_⟩
    intro v hv
    exact (chiSquaredPolicyValueCandidates_bounds R π s hv).1
  constructor
  · apply le_csInf hnonempty
    intro v hv
    exact (chiSquaredPolicyValueCandidates_bounds R π s hv).1
  · have hnominal :
      (chiSquaredAdversarialMDP R R.nominal.transition).trajectoryExpectedValue π s ∈
        chiSquaredPolicyValueCandidates R π s :=
    ⟨R.nominal.transition, chiSquaredAdmissibleKernel_nominal R, rfl⟩
    calc
      chiSquaredRobustPolicyValue R π s ≤
          (chiSquaredAdversarialMDP R R.nominal.transition).trajectoryExpectedValue π s :=
        csInf_le hbelow hnominal
      _ ≤ 1 / (1 - R.nominal.discount) :=
        ((chiSquaredAdversarialMDP R R.nominal.transition).trajectoryExpectedValue_bounds π s).2

/-- Robust value from an initial distribution, using its finite expectation of
the statewise robust value function. -/
noncomputable def chiSquaredRobustPolicyValueAtDistribution
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) : ℝ :=
  μ.expectation (chiSquaredRobustPolicyValue R π)

/-- The source optimal robust value benchmark, represented as the supremum of
the robust policy values over stationary randomized policies. Attainment is
proved below on singleton action spaces; no general attainment is assumed. -/
noncomputable def chiSquaredRobustOptimalValueAtDistribution
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (μ : FiniteDistribution State) : ℝ :=
  sSup (Set.range fun π : StationaryPolicy State Action ↦
    chiSquaredRobustPolicyValueAtDistribution R π μ)

/-- Probability vectors on a subsingleton carrier are extensionally equal. -/
theorem finiteDistribution_eq_of_subsingleton [Subsingleton Action]
    (p q : FiniteDistribution Action) : p = q := by
  cases p with
  | mk pp hp hsum =>
    cases q with
    | mk qp hq hqsum =>
      simp only [FiniteDistribution.mk.injEq]
      funext a
      have hpp : pp a = 1 := by
        simpa using (FiniteDistribution.prob_eq_one_of_subsingleton
          (⟨pp,hp,hsum⟩ : FiniteDistribution Action) a)
      have hqq : qp a = 1 := by
        simpa using (FiniteDistribution.prob_eq_one_of_subsingleton
          (⟨qp,hq,hqsum⟩ : FiniteDistribution Action) a)
      rw [hpp, hqq]

/-- Every stationary randomized policy is the same policy when there is only
one action. -/
theorem chiSquaredStationaryPolicy_eq_of_subsingleton [Subsingleton Action]
    (π₁ π₂ : StationaryPolicy State Action) : π₁ = π₂ := by
  funext s
  exact finiteDistribution_eq_of_subsingleton (π₁ s) (π₂ s)

/-- On a singleton action space, the source optimal benchmark is attained by
every stationary policy and equals its actual robust value. -/
theorem chiSquaredRobustOptimalValueAtDistribution_eq_policy
    [Subsingleton Action]
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (μ : FiniteDistribution State) (π : StationaryPolicy State Action) :
    chiSquaredRobustOptimalValueAtDistribution R μ =
      chiSquaredRobustPolicyValueAtDistribution R π μ := by
  have hrange :
      Set.range (fun π' : StationaryPolicy State Action ↦
        chiSquaredRobustPolicyValueAtDistribution R π' μ) =
          {chiSquaredRobustPolicyValueAtDistribution R π μ} := by
    ext x
    constructor
    · rintro ⟨π', rfl⟩
      rw [chiSquaredStationaryPolicy_eq_of_subsingleton π' π]
      simp
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨π, rfl⟩
  unfold chiSquaredRobustOptimalValueAtDistribution
  rw [hrange]
  simp

/-- The robust supremum is attained on a singleton action space. The nominal
MDP supplies a concrete deterministic policy witness; policy equality shows
it is robust-optimal without using a robust Bellman theorem. -/
theorem chiSquaredRobustOptimalValueAtDistribution_attained_of_subsingleton
    [Subsingleton Action]
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (μ : FiniteDistribution State) :
    ∃ π : StationaryPolicy State Action,
      chiSquaredRobustOptimalValueAtDistribution R μ =
        chiSquaredRobustPolicyValueAtDistribution R π μ := by
  exact ⟨R.nominal.optimalGreedyPolicy,
    chiSquaredRobustOptimalValueAtDistribution_eq_policy R μ
      R.nominal.optimalGreedyPolicy⟩

/-- The robust policy suboptimality gap is pointwise zero on a singleton action
space, without assuming any policy optimality theorem. -/
theorem chiSquaredRobustPolicyGap_eq_zero_of_subsingleton
    [Subsingleton Action]
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (μ : FiniteDistribution State) (π : StationaryPolicy State Action) :
    chiSquaredRobustOptimalValueAtDistribution R μ -
      chiSquaredRobustPolicyValueAtDistribution R π μ = 0 := by
  rw [chiSquaredRobustOptimalValueAtDistribution_eq_policy]
  ring

/-- For any data-to-policy estimator, the strict robust suboptimality event is
empty on a singleton action space when ε is positive. -/
theorem chiSquaredRobustPolicyFailureEvent_eq_empty_of_subsingleton
    [Subsingleton Action]
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (μ : FiniteDistribution State) {Ω : Type*}
    (estimator : Ω → StationaryPolicy State Action) {ε : ℝ} (hε : 0 < ε) :
    {ω | ε < chiSquaredRobustOptimalValueAtDistribution R μ -
      chiSquaredRobustPolicyValueAtDistribution R (estimator ω) μ} = ∅ := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rw [chiSquaredRobustPolicyGap_eq_zero_of_subsingleton R μ (estimator ω)]
  exact not_lt_of_ge hε.le

/-- The same singleton-action strict-error event has probability zero under
every measure, in particular under the product nominal-row sampling law. -/
theorem chiSquaredRobustPolicyFailureMeasure_eq_zero_of_subsingleton
    [Subsingleton Action] {Ω : Type*} [MeasurableSpace Ω]
    (R : ChiSquaredRMDP (State := State) (Action := Action))
    (μ : FiniteDistribution State) (dataLaw : MeasureTheory.Measure Ω)
    (estimator : Ω → StationaryPolicy State Action) {ε : ℝ} (hε : 0 < ε) :
    dataLaw {ω | ε < chiSquaredRobustOptimalValueAtDistribution R μ -
      chiSquaredRobustPolicyValueAtDistribution R (estimator ω) μ} = 0 := by
  rw [chiSquaredRobustPolicyFailureEvent_eq_empty_of_subsingleton R μ estimator hε]
  exact MeasureTheory.measure_empty

end StatisticalRL.RobustRL

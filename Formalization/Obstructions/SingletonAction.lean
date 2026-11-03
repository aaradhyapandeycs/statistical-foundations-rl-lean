import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Singleton-action obstruction to policy-learning lower bounds

Theorem 3.7(i), `theorem:azar`, does not explicitly exclude `A = 1` while
asserting a positive probability of positive policy loss. Section 3.3 earlier
assumes `A ≥ 2` for policy learning; whether that condition carries over to
Section 3.4 is an open interpretation question. The following observation is
independent of any particular implementation of MDP trajectories: on a
singleton action space every deterministic policy is the same function.
Consequently *any* extensional policy-evaluation map gives zero loss.

This is an obstruction lemma, not a replacement for the paper's full minimax
statement, sampling experiment, or an approved corrected theorem.
-/

namespace StatisticalRL.Obstructions

variable {State Action Ω Value : Type*} [Subsingleton Action]
  [NormedAddCommGroup Value]

/-- Any policy-evaluation function assigns identical values to deterministic
policies on a singleton action carrier. No Bellman/value identity is assumed. -/
theorem singleton_action_loss_eq_zero
    (evaluate : (State → Action) → Value)
    (estimator : Ω → State → Action) (optimal : State → Action) (ω : Ω) :
    ‖evaluate (estimator ω) - evaluate optimal‖ = 0 := by
  have hpolicy : estimator ω = optimal := by
    funext s
    exact Subsingleton.elim _ _
  simp [hpolicy]

/-- For every positive error threshold, the failure event is empty, uniformly
over the observation space and the policy estimator. -/
theorem singleton_action_failure_event_eq_empty
    (evaluate : (State → Action) → Value)
    (estimator : Ω → State → Action) (optimal : State → Action)
    {ε : ℝ} (hε : 0 < ε) :
    {ω | ε < ‖evaluate (estimator ω) - evaluate optimal‖} = ∅ := by
  ext ω
  simp only [Set.mem_setOf_eq, singleton_action_loss_eq_zero, Set.mem_empty_iff_false,
    iff_false]
  exact not_lt_of_ge hε.le

/-- In particular, the policy-loss event has probability zero under every
measure, rather than at least one quarter. This uses no distributional or
measurability assumption on the estimator, because the event is empty. -/
theorem singleton_action_failure_measure_eq_zero [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (evaluate : (State → Action) → Value)
    (estimator : Ω → State → Action) (optimal : State → Action)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε < ‖evaluate (estimator ω) - evaluate optimal‖} = 0 := by
  rw [singleton_action_failure_event_eq_empty evaluate estimator optimal hε,
    MeasureTheory.measure_empty]

/-- The source's cardinality restriction does admit sixteen states and one action. -/
theorem singleton_action_size_is_admitted :
    Fintype.card (Fin 16) * Fintype.card (Fin 1) ≥ 16 := by
  decide

end StatisticalRL.Obstructions

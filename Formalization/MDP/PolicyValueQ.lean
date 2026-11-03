import Formalization.MDP.DiscountedFiniteTrajectory

/-!
# Policy state-value and Q Bellman solutions

The source's state value is the policy average of its Q-value and both obey
Bellman consistency. This module proves those relations for the independently
constructed unique Bellman fixed points. Their identification with actual
infinite-trajectory returns remains a separate obligation.
-/

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Average an actual state-action function under the policy's action law. -/
def policyAverageQ (π : StationaryPolicy State Action) (Q : State → Action → ℝ) :
    State → ℝ := fun s ↦ (π s).expectation (Q s)

/-- Averaging any policy Q-Bellman solution gives a state Bellman solution. -/
theorem policyAverageQ_is_value_fixed (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (Q : State → Action → ℝ)
    (hQ : M.qBellman π Q = Q) :
    M.valueBellman π (policyAverageQ π Q) = policyAverageQ π Q := by
  funext s
  calc
    M.valueBellman π (policyAverageQ π Q) s =
        (π s).expectation (fun a ↦ M.qBellman π Q s a) := by
      unfold valueBellman policyTransition qBellman policyAverageQ
      rw [FiniteDistribution.expectation_bind, FiniteDistribution.expectation_add,
        FiniteDistribution.expectation_mul]
    _ = (π s).expectation (Q s) := by rw [hQ]
    _ = policyAverageQ π Q s := rfl

/-- The unique state Bellman solution equals the policy average of the unique
Q Bellman solution. -/
theorem valueFixedPoint_eq_policyAverageQ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    M.valueFixedPoint π = policyAverageQ π (M.policyFixedPoint π) := by
  symm
  exact (M.valueFixedPoint_characterization π _).mp
    (M.policyAverageQ_is_value_fixed π _ (M.policyFixedPoint_spec π))

/-- Policy Q consistency expressed through the independently constructed
state Bellman solution. -/
theorem policyFixedPoint_eq_reward_add_value (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    M.policyFixedPoint π s a = M.reward s a + M.discount *
      (M.transition s a).expectation (M.valueFixedPoint π) := by
  have h := congrFun (congrFun (M.policyFixedPoint_spec π) s) a
  change M.reward s a + M.discount *
    (M.transition s a).expectation (policyAverageQ π (M.policyFixedPoint π)) =
      M.policyFixedPoint π s a at h
  rw [M.valueFixedPoint_eq_policyAverageQ π]
  exact h.symm

end StatisticalRL.DiscountedMDP

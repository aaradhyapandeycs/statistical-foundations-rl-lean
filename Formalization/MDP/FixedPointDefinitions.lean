import Formalization.MDP.FixedPointExistence

namespace StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The policy Bellman solution, selected only after proving exact existence and uniqueness. -/
noncomputable def policyFixedPoint (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : State → Action → ℝ :=
  Classical.choose (M.policy_fixedPoint_exists_unique π)

/-- The optimality Bellman solution, without assuming a trajectory-value interpretation. -/
noncomputable def optimalityFixedPoint (M : DiscountedMDP State Action) :
    State → Action → ℝ :=
  Classical.choose M.optimality_fixedPoint_exists_unique


end StatisticalRL.DiscountedMDP

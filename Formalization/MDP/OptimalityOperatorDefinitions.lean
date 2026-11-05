import Formalization.MDP.CoreDefinitions

namespace StatisticalRL
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The genuine maximum over a nonempty finite action set. -/
noncomputable def actionMaximum {Action : Type*} [Fintype Action] [Nonempty Action]
    (f : Action → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

namespace DiscountedMDP

/-- The source's Bellman optimality operator, `eq:bellman_optimality_operator`. -/
noncomputable def qOptimality (M : DiscountedMDP State Action)
    (Q : State → Action → ℝ) (s : State) (a : Action) : ℝ :=
  letI : Nonempty Action := M.action_nonempty
  M.reward s a + M.discount * (M.transition s a).expectation (fun t ↦ actionMaximum (Q t))

end DiscountedMDP
end StatisticalRL

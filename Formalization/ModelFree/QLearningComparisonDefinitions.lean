import Formalization.MDP.Basic

namespace StatisticalRL.QLearning
variable {State : Type*} [Fintype State]

/-- Finite max-minus-min span: the minimum is the negative maximum of -v. -/
noncomputable def qChiValueSpan [Nonempty State] (v : State → ℝ) : ℝ :=
  actionMaximum v + actionMaximum (fun x ↦ -v x)

end StatisticalRL.QLearning

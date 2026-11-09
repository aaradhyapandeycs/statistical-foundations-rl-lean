import Formalization.ModelFree.QLearningUnderestimationLift
import Formalization.MDP.OptimalTrajectoryValue

/-! value identity. The lifted chain's value at `(s,a)` is `Q^f(s,a)`, and
`Q^f = Q⋆` when `f` is optimal in the sense `V^f = V⋆` at every state. -/

namespace StatisticalRL.QLearning
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Equal state values give equal actual forced-action Q-values. -/
theorem trajectoryExpectedQ_eq_of_trajectoryExpectedValue_eq (M : DiscountedMDP State Action)
    (π₁ π₂ : StationaryPolicy State Action)
    (h : ∀ s, M.trajectoryExpectedValue π₁ s = M.trajectoryExpectedValue π₂ s)
    (s : State) (a : Action) :
    M.trajectoryExpectedQ π₁ s a = M.trajectoryExpectedQ π₂ s a := by
  have hV : M.trajectoryExpectedValue π₁ = M.trajectoryExpectedValue π₂ := funext h
  rw [M.trajectoryExpectedQ_eq_policyFixedPoint, M.trajectoryExpectedQ_eq_policyFixedPoint,
    M.policyFixedPoint_eq_reward_add_value, M.policyFixedPoint_eq_reward_add_value,
    ← M.trajectoryExpectedValue_eq_valueFixedPoint,
    ← M.trajectoryExpectedValue_eq_valueFixedPoint, hV]

/-- The lifted chain evaluates the deterministic policy `f`: its actual trajectory value
at `(s,a)` is the actual forced-action value `Q^f(s,a)`. -/
theorem qPolicyLift_trajectoryExpectedValue (M : DiscountedMDP State Action)
    (f : State → Action) (x : State × Action) :
    (qPolicyLiftMDP M f).trajectoryExpectedValue qPolicyLiftPolicy x =
      M.trajectoryExpectedQ (fun s ↦ EnvironmentStage.pointMass (f s)) x.1 x.2 := by
  set πf : StationaryPolicy State Action := fun s ↦ EnvironmentStage.pointMass (f s)
  set Y : State × Action → Unit → ℝ := fun y _ ↦ M.trajectoryExpectedQ πf y.1 y.2
  have hY : (qPolicyLiftMDP M f).qBellman qPolicyLiftPolicy Y = Y := by
    funext y u
    have hb := congrFun (congrFun (M.trajectoryExpectedQ_bellman πf) y.1) y.2
    change M.reward y.1 y.2 + M.discount * (qPolicyLiftTransition M f y.1 y.2).expectation
      (fun z ↦ (EnvironmentStage.pointMass ()).expectation (Y z)) =
        M.trajectoryExpectedQ πf y.1 y.2
    rw [← hb, qPolicyLift_expectation]
    unfold qBellman
    simp only [EnvironmentStage.expectation_pointMass, Y, πf]
  have hfix := ((qPolicyLiftMDP M f).policyFixedPoint_characterization
    qPolicyLiftPolicy Y).mp hY
  have hQ : ∀ u, (qPolicyLiftMDP M f).trajectoryExpectedQ qPolicyLiftPolicy x u = Y x u :=
    fun u ↦ by rw [(qPolicyLiftMDP M f).trajectoryExpectedQ_eq_policyFixedPoint, ← hfix]
  rw [(qPolicyLiftMDP M f).trajectoryExpectedValue_eq_policyAverageQ]
  change (EnvironmentStage.pointMass ()).expectation _ = _
  rw [EnvironmentStage.expectation_pointMass, hQ]

/-- With `f` optimal (`V^f = V⋆`), the lifted chain's value is `Q⋆`. -/
theorem qPolicyLift_trajectoryExpectedValue_optimal (M : DiscountedMDP State Action)
    (f : State → Action)
    (hf : ∀ s, M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (f x)) s =
      M.trajectoryExpectedValue M.optimalGreedyPolicy s) (x : State × Action) :
    (qPolicyLiftMDP M f).trajectoryExpectedValue qPolicyLiftPolicy x =
      M.trajectoryExpectedQ M.optimalGreedyPolicy x.1 x.2 := by
  rw [qPolicyLift_trajectoryExpectedValue]
  exact trajectoryExpectedQ_eq_of_trajectoryExpectedValue_eq M _ _ hf x.1 x.2

end StatisticalRL.QLearning

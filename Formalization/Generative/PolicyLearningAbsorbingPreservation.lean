import Formalization.Generative.PolicyLearningAbsorbing

import Formalization.Statements.Ch3Definitions
/-! Source Lemma `LemAbsToNormalV`: the absorbing model at the original optimal
trajectory value has the same optimal trajectory values everywhere. -/

namespace StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance preservationStateDecidable : DecidableEq State := Classical.decEq State

/-- Its state value is the maximum of the original optimal Q fixed point. -/
theorem optimalTrajectoryValue_eq_actionMaximum (M : DiscountedMDP State Action) (s : State) :
    optimalTrajectoryValue M s =
      letI : Nonempty Action := M.action_nonempty
      actionMaximum (M.optimalityFixedPoint s) := by
  letI : Nonempty Action := M.action_nonempty
  unfold optimalTrajectoryValue
  rw [M.trajectoryExpectedValue_eq_policyAverageQ]
  change (EnvironmentStage.pointMass (M.optimalGreedyAction s)).expectation
    (M.trajectoryExpectedQ M.optimalGreedyPolicy s) = _
  rw [EnvironmentStage.expectation_pointMass, M.optimalGreedy_trajectoryQ,
    M.optimalGreedyAction_max]

/-- Candidate optimal Q for the absorbing model: the old optimal Q away from x,
and the common value V*(x) for all actions at x. -/
noncomputable def preservedOptimalQ (M : DiscountedMDP State Action) (x : State) :
    State → Action → ℝ := fun s a ↦
  if s = x then optimalTrajectoryValue M x else M.optimalityFixedPoint s a

/-- The candidate has exactly the original optimal value at every state. -/
theorem preservedOptimalQ_actionMaximum (M : DiscountedMDP State Action) (x s : State) :
    letI : Nonempty Action := M.action_nonempty
    actionMaximum (preservedOptimalQ M x s) = optimalTrajectoryValue M s := by
  letI : Nonempty Action := M.action_nonempty
  by_cases hs : s = x
  · subst s
    simp [preservedOptimalQ, actionMaximum]
  · rw [optimalTrajectoryValue_eq_actionMaximum M s]
    congr 1
    funext a
    simp [preservedOptimalQ, hs]

/-- The candidate Q obeys the absorbing model's optimal Bellman equation. -/
theorem preservedOptimalQ_bellman (M : DiscountedMDP State Action) (x : State) :
    (optimalValueAbsorbingModel M x).qOptimality (preservedOptimalQ M x) =
      preservedOptimalQ M x := by
  letI : Nonempty Action := M.action_nonempty
  let H := optimalValueAbsorbingModel M x
  have hmax : (fun s ↦ actionMaximum (preservedOptimalQ M x s)) = optimalTrajectoryValue M := by
    funext s
    exact preservedOptimalQ_actionMaximum M x s
  funext s a
  change H.reward s a + H.discount * (H.transition s a).expectation
    (fun t ↦ actionMaximum (preservedOptimalQ M x t)) = preservedOptimalQ M x s a
  rw [hmax]
  by_cases hs : s = x
  · subst s
    simp [H, optimalValueAbsorbingModel, stateAbsorbingModel, preservedOptimalQ]
    ring
  · have hopt := congrFun (congrFun M.optimalityFixedPoint_spec s) a
    change M.reward s a + M.discount * (M.transition s a).expectation
      (fun t ↦ actionMaximum (M.optimalityFixedPoint t)) = M.optimalityFixedPoint s a at hopt
    have hv : optimalTrajectoryValue M = fun t ↦ actionMaximum (M.optimalityFixedPoint t) := by
      funext t
      exact optimalTrajectoryValue_eq_actionMaximum M t
    simp only [H, optimalValueAbsorbingModel, stateAbsorbingModel, hs, ↓reduceIte, preservedOptimalQ]
    rw [hv]
    exact hopt

/-- Source Lemma `LemAbsToNormalV` for actual infinite-trajectory values. -/
theorem optimalValueAbsorbingModel_preserves_optimalTrajectoryValue
    (M : DiscountedMDP State Action) (x s : State) :
    optimalTrajectoryValue (optimalValueAbsorbingModel M x) s = optimalTrajectoryValue M s := by
  letI : Nonempty Action := M.action_nonempty
  let H := optimalValueAbsorbingModel M x
  have hQ : preservedOptimalQ M x = H.optimalityFixedPoint :=
    (H.optimalityFixedPoint_characterization _).mp (preservedOptimalQ_bellman M x)
  rw [optimalTrajectoryValue_eq_actionMaximum H s, ← hQ]
  exact preservedOptimalQ_actionMaximum M x s

/-- The same source identity applies pointwise to every empirical model. -/
theorem empirical_absorbing_preserves_optimalTrajectoryValue
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (x s : State) :
    optimalTrajectoryValue (optimalValueAbsorbingModel (empiricalModel M N hN data) x) s =
      optimalTrajectoryValue (empiricalModel M N hN data) s :=
  optimalValueAbsorbingModel_preserves_optimalTrajectoryValue (empiricalModel M N hN data) x s

/-- The empirical model's actual optimal trajectory value is exactly the
model-based policy-learning algorithm's value estimator. -/
theorem empirical_optimalTrajectoryValue_eq_valueEstimator
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) :
    optimalTrajectoryValue (empiricalModel M N hN data) = valueEstimator M N hN data := by
  rfl

/-- The absorbing model built at the empirical optimum preserves the actual
empirical value estimator at every state. -/
theorem empirical_absorbing_preserves_valueEstimator
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (x s : State) :
    optimalTrajectoryValue (optimalValueAbsorbingModel (empiricalModel M N hN data) x) s =
      valueEstimator M N hN data s := by
  rw [empirical_absorbing_preserves_optimalTrajectoryValue,
    empirical_optimalTrajectoryValue_eq_valueEstimator]

end StatisticalRL.ModelBasedPolicyLearning

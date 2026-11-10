import Formalization.Generative.ModelBasedPolicyLearning

import Formalization.Generative.ModelBasedDefinitions
/-!
# State-absorbing leave-one-out model

This file constructs the exact model in `eqn:transition-kernel-M-su-inf`
and `eqn:reward-M-su-inf`, and proves basic trajectory and data-invariance
properties. It does not yet prove the source's complete value-preservation
lemma or statistical independence.
-/

namespace StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance absorbingStateDecidable : DecidableEq State := Classical.decEq State

/-- The replaced state's transition really is the point mass at that state. -/
theorem stateAbsorbingModel_transition_at (M : DiscountedMDP State Action)
    (x : State) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / (1 - M.discount)) (a : Action) :
    (stateAbsorbingModel M x u hu0 hu1).transition x a = EnvironmentStage.pointMass x := by
  simp [stateAbsorbingModel]

/-- Each other transition row is exactly the original one. -/
theorem stateAbsorbingModel_transition_away (M : DiscountedMDP State Action)
    (x : State) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / (1 - M.discount))
    (s : State) (a : Action) (hs : s ≠ x) :
    (stateAbsorbingModel M x u hu0 hu1).transition s a = M.transition s a := by
  simp [stateAbsorbingModel, hs]

/-- The actual infinite-trajectory value at the absorbing state is exactly u,
for every stationary randomized policy. -/
theorem stateAbsorbingModel_trajectoryValue_at (M : DiscountedMDP State Action)
    (x : State) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / (1 - M.discount))
    (π : StationaryPolicy State Action) :
    (stateAbsorbingModel M x u hu0 hu1).trajectoryExpectedValue π x = u := by
  let H := stateAbsorbingModel M x u hu0 hu1
  have h := congrFun (H.valueFixedPoint_spec π) x
  rw [← H.trajectoryExpectedValue_eq_valueFixedPoint π] at h
  simp only [DiscountedMDP.valueBellman, DiscountedMDP.policyTransition] at h
  have hr : H.reward x = fun _ ↦ (1 - M.discount) * u := by
    funext a
    simp [H, stateAbsorbingModel]
  have ht : H.transition x = fun _ ↦ EnvironmentStage.pointMass x := by
    funext a
    exact stateAbsorbingModel_transition_at M x u hu0 hu1 a
  rw [hr, ht] at h
  change (π x).expectation (fun _ ↦ (1 - M.discount) * u) +
      M.discount * ((π x).bind (fun _ ↦ EnvironmentStage.pointMass x)).expectation
        (H.trajectoryExpectedValue π) = H.trajectoryExpectedValue π x at h
  rw [FiniteDistribution.expectation_const, FiniteDistribution.expectation_bind] at h
  simp only [EnvironmentStage.expectation_pointMass, FiniteDistribution.expectation_const] at h
  have hd : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  nlinarith

/-- For fixed u, changing data at the removed state does not alter any
transition row of the empirical absorbing model. -/
theorem absorbingEmpirical_transition_eq_of_data_eq_away
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data data' : Samples State Action N) (x : State) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / (1 - M.discount))
    (hdata : ∀ s a i, s ≠ x → data ((s,a),i) = data' ((s,a),i))
    (s : State) (a : Action) :
    (stateAbsorbingModel (empiricalModel M N hN data) x u hu0 hu1).transition s a =
    (stateAbsorbingModel (empiricalModel M N hN data') x u hu0 hu1).transition s a := by
  by_cases hs : s = x
  · subst s
    simp [stateAbsorbingModel]
  · simp only [stateAbsorbingModel_transition_away _ _ _ _ _ _ _ hs]
    change empiricalRow N hN data s a = empiricalRow N hN data' s a
    have hv : (fun i ↦ data ((s,a),i)) = (fun i ↦ data' ((s,a),i)) := by
      funext i
      exact hdata s a i hs
    unfold empiricalRow
    rw [hv]

/-- For fixed u, changing only samples at x leaves the absorbing empirical
model's optimal Q fixed point unchanged. This is deterministic invariance,
not yet a probabilistic independence theorem. -/
theorem absorbingEmpirical_optimalQ_eq_of_data_eq_away
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data data' : Samples State Action N) (x : State) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / (1 - M.discount))
    (hdata : ∀ s a i, s ≠ x → data ((s,a),i) = data' ((s,a),i)) :
    (stateAbsorbingModel (empiricalModel M N hN data) x u hu0 hu1).optimalityFixedPoint =
    (stateAbsorbingModel (empiricalModel M N hN data') x u hu0 hu1).optimalityFixedPoint := by
  let H := stateAbsorbingModel (empiricalModel M N hN data) x u hu0 hu1
  let H' := stateAbsorbingModel (empiricalModel M N hN data') x u hu0 hu1
  have ht (s : State) (a : Action) : H.transition s a = H'.transition s a :=
    absorbingEmpirical_transition_eq_of_data_eq_away M N hN data data' x u hu0 hu1 hdata s a
  have hr : H.reward = H'.reward := rfl
  have hd : H.discount = H'.discount := rfl
  have he : H'.qOptimality H.optimalityFixedPoint = H.qOptimality H.optimalityFixedPoint := by
    funext s a
    simp only [DiscountedMDP.qOptimality, ← hr, ← hd, ← ht s a]
  apply (H'.optimalityFixedPoint_characterization H.optimalityFixedPoint).mp
  rw [he]
  exact H.optimalityFixedPoint_spec

/-- Fixed-u leave-one-out invariance holds for the actual optimal trajectory
value function, even when the two empirical greedy actions are chosen separately. -/
theorem absorbingEmpirical_optimalValue_eq_of_data_eq_away
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data data' : Samples State Action N) (x : State) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / (1 - M.discount))
    (hdata : ∀ s a i, s ≠ x → data ((s,a),i) = data' ((s,a),i))
    (s : State) :
    let H := stateAbsorbingModel (empiricalModel M N hN data) x u hu0 hu1
    let H' := stateAbsorbingModel (empiricalModel M N hN data') x u hu0 hu1
    H.trajectoryExpectedValue H.optimalGreedyPolicy s =
      H'.trajectoryExpectedValue H'.optimalGreedyPolicy s := by
  letI : Nonempty Action := M.action_nonempty
  let H := stateAbsorbingModel (empiricalModel M N hN data) x u hu0 hu1
  let H' := stateAbsorbingModel (empiricalModel M N hN data') x u hu0 hu1
  have hv (K : DiscountedMDP State Action) :
      K.trajectoryExpectedValue K.optimalGreedyPolicy s = actionMaximum (K.optimalityFixedPoint s) := by
    rw [K.trajectoryExpectedValue_eq_policyAverageQ]
    change (EnvironmentStage.pointMass (K.optimalGreedyAction s)).expectation
      (K.trajectoryExpectedQ K.optimalGreedyPolicy s) = _
    rw [EnvironmentStage.expectation_pointMass, K.optimalGreedy_trajectoryQ,
      K.optimalGreedyAction_max]
  change H.trajectoryExpectedValue H.optimalGreedyPolicy s =
    H'.trajectoryExpectedValue H'.optimalGreedyPolicy s
  rw [hv H, hv H']
  have hq := absorbingEmpirical_optimalQ_eq_of_data_eq_away M N hN data data' x u hu0 hu1 hdata
  change H.optimalityFixedPoint = H'.optimalityFixedPoint at hq
  rw [hq]

end StatisticalRL.ModelBasedPolicyLearning

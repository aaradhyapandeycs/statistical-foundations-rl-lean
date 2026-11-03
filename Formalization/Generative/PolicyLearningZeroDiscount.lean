import Formalization.Generative.ModelBasedPolicyLearning

/-! Zero-discount exact policy learning under the actual generative experiment. -/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance zeroDiscountStateMeasurable : MeasurableSpace State := ⊤

/-- Every true trajectory Q equals the immediate reward at discount zero. -/
theorem trajectoryQ_zero_discount (M : DiscountedMDP State Action)
    (hγ : M.discount = 0) (π : StationaryPolicy State Action) (s : State) (a : Action) :
    M.trajectoryExpectedQ π s a = M.reward s a := by
  rw [M.trajectoryExpectedQ_eq_policyFixedPoint]
  have h := congrFun (congrFun (M.policyFixedPoint_spec π) s) a
  change M.reward s a + M.discount * _ = M.policyFixedPoint π s a at h
  simpa [hγ] using h.symm

/-- At discount zero the optimal Q fixed point is the reward table. -/
theorem optimalQ_zero_discount (M : DiscountedMDP State Action)
    (hγ : M.discount = 0) : M.optimalityFixedPoint = M.reward := by
  funext s a
  have h := congrFun (congrFun M.optimalityFixedPoint_spec s) a
  change M.reward s a + M.discount * _ = M.optimalityFixedPoint s a at h
  simpa [hγ] using h.symm

/-- A greedy optimal action attains the greatest immediate reward. -/
theorem greedy_reward_zero_discount (M : DiscountedMDP State Action)
    (hγ : M.discount = 0) (s : State) :
    M.reward s (M.optimalGreedyAction s) =
      letI : Nonempty Action := M.action_nonempty
      actionMaximum (M.reward s) := by
  have h := M.optimalGreedyAction_max s
  rw [optimalQ_zero_discount M hγ] at h
  exact h

/-- On every sample, the output policy's true Q agrees with the true optimal Q. -/
theorem policyEstimator_trueQ_zero_discount (M : DiscountedMDP State Action)
    (hγ : M.discount = 0) (N : ℕ) (hN : 0 < N) (data : Samples State Action N)
    (s : State) (a : Action) :
    M.trajectoryExpectedQ
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s a =
      M.trajectoryExpectedQ M.optimalGreedyPolicy s a := by
  rw [trajectoryQ_zero_discount M hγ, trajectoryQ_zero_discount M hγ]

/-- On every sample, the output policy's true state value is optimal. -/
theorem policyEstimator_trueValue_zero_discount (M : DiscountedMDP State Action)
    (hγ : M.discount = 0) (N : ℕ) (hN : 0 < N) (data : Samples State Action N)
    (s : State) :
    M.trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s =
      M.trajectoryExpectedValue M.optimalGreedyPolicy s := by
  let E := empiricalModel M N hN data
  have hE : E.discount = 0 := hγ
  have hmax := greedy_reward_zero_discount E hE s
  change M.reward s (policyEstimator M N hN data s) =
    letI : Nonempty Action := M.action_nonempty
    actionMaximum (M.reward s) at hmax
  have htrue := greedy_reward_zero_discount M hγ s
  rw [M.trajectoryExpectedValue_eq_policyAverageQ, M.trajectoryExpectedValue_eq_policyAverageQ]
  change (EnvironmentStage.pointMass (policyEstimator M N hN data s)).expectation
      (M.trajectoryExpectedQ _ s) =
    (EnvironmentStage.pointMass (M.optimalGreedyAction s)).expectation
      (M.trajectoryExpectedQ _ s)
  rw [EnvironmentStage.expectation_pointMass, EnvironmentStage.expectation_pointMass,
    trajectoryQ_zero_discount M hγ, trajectoryQ_zero_discount M hγ]
  exact hmax.trans htrue.symm

/-- Both full-array true losses are zero on every outcome. -/
theorem policyEstimator_loss_zero_discount (M : DiscountedMDP State Action)
    (hγ : M.discount = 0) (N : ℕ) (hN : 0 < N) (data : Samples State Action N) :
    ‖(fun s ↦ M.trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s) -
      M.trajectoryExpectedValue M.optimalGreedyPolicy‖ = 0 ∧
    ‖(fun s a ↦ M.trajectoryExpectedQ
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s a) -
      M.trajectoryExpectedQ M.optimalGreedyPolicy‖ = 0 := by
  constructor
  · have heq : (fun s ↦ M.trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s) =
        M.trajectoryExpectedValue M.optimalGreedyPolicy := by
      funext s
      exact policyEstimator_trueValue_zero_discount M hγ N hN data s
    rw [heq, sub_self, norm_zero]
  · have heq : (fun s a ↦ M.trajectoryExpectedQ
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s a) =
        M.trajectoryExpectedQ M.optimalGreedyPolicy := by
      funext s a
      exact policyEstimator_trueQ_zero_discount M hγ N hN data s a
    rw [heq, sub_self, norm_zero]

/-- The exact joint success event has probability one under the true sample law. -/
theorem policyEstimator_success_zero_discount (M : DiscountedMDP State Action)
    (hγ : M.discount = 0) (N : ℕ) (hN : 0 < N) :
    (samplingLaw M N).real {data |
      ‖(fun s ↦ M.trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s) -
          M.trajectoryExpectedValue M.optimalGreedyPolicy‖ = 0 ∧
      ‖(fun s a ↦ M.trajectoryExpectedQ
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s a) -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖ = 0} = 1 := by
  have heq : {data : Samples State Action N |
      ‖(fun s ↦ M.trajectoryExpectedValue
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s) -
          M.trajectoryExpectedValue M.optimalGreedyPolicy‖ = 0 ∧
      ‖(fun s a ↦ M.trajectoryExpectedQ
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s a) -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖ = 0} = Set.univ := by
    ext data
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact policyEstimator_loss_zero_discount M hγ N hN data
  rw [heq, probReal_univ]

end StatisticalRL.ModelBasedPolicyLearning

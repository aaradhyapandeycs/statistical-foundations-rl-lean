import Formalization.Generative.PolicyEvaluationSourceTheorem
import Formalization.Generative.PolicyLearningHoeffding

/-! Fixed deterministic policy projection from the learning experiment. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.ModelBasedPolicyLearning
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance fixedProjectionStateMeasurable : MeasurableSpace State := ⊤

/-- Keep the samples from the fixed action selected at each state. -/
def projectPolicySamples (N : ℕ) (f : State → Action) (data : Samples State Action N) :
    ModelBasedPolicyEvaluation.Samples State N := fun i ↦ data ((i.1, f i.1), i.2)

theorem deterministic_policyTransition_eq (M : DiscountedMDP State Action)
    (f : State → Action) (s : State) :
    M.policyTransition (fun t ↦ EnvironmentStage.pointMass (f t)) s = M.transition s (f s) := by
  have hp : (M.policyTransition (fun t ↦ EnvironmentStage.pointMass (f t)) s).prob =
      (M.transition s (f s)).prob := by
    funext t
    change (EnvironmentStage.pointMass (f s)).expectation (fun a ↦ (M.transition s a).prob t) = _
    exact EnvironmentStage.expectation_pointMass (f s) (fun a ↦ (M.transition s a).prob t)
  cases h₁ : (M.policyTransition (fun t ↦ EnvironmentStage.pointMass (f t)) s) with
  | mk p pp ps =>
    cases h₂ : (M.transition s (f s)) with
    | mk q qp qs =>
      simp only [h₁, h₂] at hp
      cases hp
      rfl

theorem samplingLaw_projectPolicySamples (M : DiscountedMDP State Action)
    (N : ℕ) (f : State → Action) :
    (samplingLaw M N).map (projectPolicySamples N f) =
      ModelBasedPolicyEvaluation.samplingLaw M (fun t ↦ EnvironmentStage.pointMass (f t)) N := by
  let j : State × Fin N → (State × Action) × Fin N := fun i ↦ ((i.1, f i.1), i.2)
  have hj : Function.Injective j := by
    intro x y h
    have hs := congrArg (fun z : (State × Action) × Fin N ↦ z.1.1) h
    have hi := congrArg (fun z : (State × Action) × Fin N ↦ z.2) h
    exact Prod.ext hs hi
  have hind := (samplingLaw_independent M N).precomp hj
  have hm : ∀ i : State × Fin N, AEMeasurable
      (fun data : Samples State Action N ↦ data (j i)) (samplingLaw M N) :=
    fun i ↦ (measurable_pi_apply (j i)).aemeasurable
  change (samplingLaw M N).map (fun data i ↦ data (j i)) = _
  rw [(iIndepFun_iff_map_fun_eq_pi_map hm).mp hind]
  unfold ModelBasedPolicyEvaluation.samplingLaw
  congr 1
  funext i
  rw [samplingLaw_marginal, deterministic_policyTransition_eq]

theorem projectedPolicy_value_eq (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) (f : State → Action) :
    (empiricalModel M N hN data).trajectoryExpectedValue
      (fun t ↦ EnvironmentStage.pointMass (f t)) =
    ModelBasedPolicyEvaluation.valueEstimator M (fun t ↦ EnvironmentStage.pointMass (f t))
      N hN (projectPolicySamples N f data) := by
  apply ModelBasedPolicyEvaluation.valueEstimator_unique
  intro s
  let H := empiricalModel M N hN data
  let π := fun t ↦ EnvironmentStage.pointMass (f t)
  have hh := congrFun (H.valueFixedPoint_spec π) s
  rw [← H.trajectoryExpectedValue_eq_valueFixedPoint π] at hh
  change (π s).expectation (H.reward s) + H.discount *
    (H.policyTransition π s).expectation (H.trajectoryExpectedValue π) =
      H.trajectoryExpectedValue π s at hh
  rw [deterministic_policyTransition_eq, EnvironmentStage.expectation_pointMass] at hh
  simpa [H, π, ModelBasedPolicyEvaluation.empiricalPolicyRow, empiricalRow, projectPolicySamples,
    EnvironmentStage.expectation_pointMass] using hh.symm

/-- Fixed true-optimal-policy evaluation under the original learning law.
The displayed budget is the policy-evaluation source budget at confidence δ/2. -/
theorem trueOptimalPolicy_evaluation_event (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / (1 - M.discount))
    (hbudget : 720 * Real.log (Fintype.card State / ((δ / 2) * (1 - M.discount))) /
      ((1 - M.discount) ^ 3 * ε ^ 2) ≤ N) :
    1 - δ / 2 < (samplingLaw M N).real {data |
      ‖(empiricalModel M N hN data).trajectoryExpectedValue M.optimalGreedyPolicy -
        M.trajectoryExpectedValue M.optimalGreedyPolicy‖ ≤ ε} := by
  let f := M.optimalGreedyAction
  let π := fun t ↦ EnvironmentStage.pointMass (f t)
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ21 : δ / 2 < 1 := by linarith
  obtain ⟨hN', hp⟩ := ModelBasedPolicyEvaluation.valueEstimator_source_sample_bound
    M π N (δ / 2) ε hδ2 hδ21 hε hεmax hbudget
  have heq : hN' = hN := Subsingleton.elim _ _
  subst hN'
  let target : Set (ModelBasedPolicyEvaluation.Samples State N) := {data |
    ‖ModelBasedPolicyEvaluation.valueEstimator M π N hN data -
      M.trajectoryExpectedValue π‖ ≤ ε}
  have hmeas : MeasurableSet target := (Set.to_countable _).measurableSet
  rw [← samplingLaw_projectPolicySamples M N f, measureReal_def,
    Measure.map_apply (measurable_of_countable _) hmeas] at hp
  convert hp using 1
  congr 2
  ext data
  change (‖(empiricalModel M N hN data).trajectoryExpectedValue π -
      M.trajectoryExpectedValue π‖ ≤ ε) ↔ _
  rw [projectedPolicy_value_eq]
  rfl

end StatisticalRL.ModelBasedPolicyLearning

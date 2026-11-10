import Formalization.Probability.EmpiricalRow
import Formalization.MDP.PrefixValueBridge

import Formalization.Generative.ModelBasedDefinitions
/-!
# Model-based evaluation of a fixed policy

The experiment draws independent observations from the policy-induced row for
all states. Empirical frequencies are then used in the discounted Bellman
solution with the known policy-averaged rewards. No error guarantee is assumed.
Source: model-based chapter, `alg:policy-eval-model-based`, lines 78–130.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyEvaluation

variable {State Action : Type*} [Fintype State] [Fintype Action]

local instance stateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance stateDecidable : DecidableEq State := Classical.decEq State

instance samplingLaw_probability (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) : IsProbabilityMeasure (samplingLaw M π N) := by
  unfold samplingLaw
  infer_instance

theorem samplingLaw_marginal (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (i : State × Fin N) :
    (samplingLaw M π N).map (fun data ↦ data i) =
      (M.policyTransition π i.1).rowMeasure := by
  exact (measurePreserving_eval (fun i : State × Fin N ↦
    (M.policyTransition π i.1).rowMeasure) i).map_eq

theorem samplingLaw_independent (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) :
    iIndepFun (fun i (data : Samples State N) ↦ data i) (samplingLaw M π N) := by
  exact iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)

theorem empiricalPolicyRow_expectation (N : ℕ) (hN : 0 < N)
    (data : Samples State N) (s : State) (V : State → ℝ) :
    (empiricalPolicyRow N hN data s).expectation V =
      (N : ℝ)⁻¹ * ∑ i : Fin N, V (data (s, i)) :=
  FiniteDistribution.empiricalRow_expectation N hN (fun i ↦ data (s, i)) V

/-- The estimator satisfies the empirical policy Bellman equation. -/
theorem valueEstimator_bellman (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) (s : State) :
    valueEstimator M π N hN data s = (π s).expectation (M.reward s) +
      M.discount * (empiricalPolicyRow N hN data s).expectation
        (valueEstimator M π N hN data) := by
  have h := congrFun ((empiricalModel M π N hN data).valueFixedPoint_spec π) s
  change (π s).expectation (fun _ ↦ (π s).expectation (M.reward s)) +
    M.discount * ((π s).bind (fun _ ↦ empiricalPolicyRow N hN data s)).expectation
      (valueEstimator M π N hN data) = valueEstimator M π N hN data s at h
  rw [FiniteDistribution.expectation_const, FiniteDistribution.expectation_bind,
    FiniteDistribution.expectation_const] at h
  exact h.symm

/-- The empirical Bellman equation uniquely specifies the plug-in estimate. -/
theorem valueEstimator_unique (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) (V : State → ℝ)
    (hV : ∀ s, V s = (π s).expectation (M.reward s) +
      M.discount * (empiricalPolicyRow N hN data s).expectation V) :
    V = valueEstimator M π N hN data := by
  apply ((empiricalModel M π N hN data).valueFixedPoint_characterization π V).mp
  funext s
  change (π s).expectation (fun _ ↦ (π s).expectation (M.reward s)) +
    M.discount * ((π s).bind (fun _ ↦ empiricalPolicyRow N hN data s)).expectation V = V s
  rw [FiniteDistribution.expectation_const, FiniteDistribution.expectation_bind,
    FiniteDistribution.expectation_const]
  exact (hV s).symm

/-- The estimator is measurable in the finite sample data. -/
theorem valueEstimator_measurable (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N) :
    Measurable (valueEstimator M π N hN) := by
  exact measurable_of_countable _

/-- The estimator equals the actual trajectory value in the empirical model. -/
theorem valueEstimator_eq_trajectory (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) :
    valueEstimator M π N hN data =
      (empiricalModel M π N hN data).trajectoryExpectedValue π := by
  exact ((empiricalModel M π N hN data).trajectoryExpectedValue_eq_valueFixedPoint π).symm

end StatisticalRL.ModelBasedPolicyEvaluation

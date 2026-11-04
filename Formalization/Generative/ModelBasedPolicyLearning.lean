import Formalization.Probability.EmpiricalRow
import Formalization.MDP.OptimalTrajectoryValue

import Formalization.Statements.Ch3Definitions
/-!
# Model-based policy learning with a generative model

The actual independent product experiment provides N next-state samples for each
state-action pair. Empirical frequency rows and known rewards define an empirical
MDP; its greedy policy is optimal for actual empirical trajectory values.
Source: `alg:policy-learn-model-based`, model-based chapter lines 814–865.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

local instance stateMeasurable : MeasurableSpace State := ⊤
local instance actionMeasurable : MeasurableSpace Action := ⊤
noncomputable local instance stateDecidable : DecidableEq State := Classical.decEq State

instance samplingLaw_probability (M : DiscountedMDP State Action) (N : ℕ) :
    IsProbabilityMeasure (samplingLaw M N) := by
  unfold samplingLaw
  infer_instance

theorem samplingLaw_marginal (M : DiscountedMDP State Action) (N : ℕ)
    (i : (State × Action) × Fin N) :
    (samplingLaw M N).map (fun data ↦ data i) = (M.transition i.1.1 i.1.2).rowMeasure := by
  exact (measurePreserving_eval (fun i : (State × Action) × Fin N ↦
    (M.transition i.1.1 i.1.2).rowMeasure) i).map_eq

theorem samplingLaw_independent (M : DiscountedMDP State Action) (N : ℕ) :
    iIndepFun (fun i (data : Samples State Action N) ↦ data i) (samplingLaw M N) := by
  exact iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)

omit [Fintype Action] in
theorem empiricalRow_expectation (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (s : State) (a : Action) (V : State → ℝ) :
    (empiricalRow N hN data s a).expectation V =
      (N : ℝ)⁻¹ * ∑ i : Fin N, V (data ((s, a), i)) :=
  FiniteDistribution.empiricalRow_expectation N hN (fun i ↦ data ((s, a), i)) V

theorem qEstimator_measurable (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) :
    Measurable (qEstimator M N hN) := by
  exact measurable_of_countable _

theorem policyEstimator_measurable (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) :
    Measurable (policyEstimator M N hN) := by
  exact measurable_of_countable _

theorem valueEstimator_measurable (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N) :
    Measurable (valueEstimator M N hN) := by
  exact measurable_of_countable _

/-- The empirical optimal Q is the unique solution of its Bellman equation. -/
theorem qEstimator_bellman (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) :
    (empiricalModel M N hN data).qOptimality (qEstimator M N hN data) =
      qEstimator M N hN data :=
  (empiricalModel M N hN data).optimalityFixedPoint_spec

theorem qEstimator_unique (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (Q : State → Action → ℝ)
    (hQ : (empiricalModel M N hN data).qOptimality Q = Q) :
    Q = qEstimator M N hN data :=
  ((empiricalModel M N hN data).optimalityFixedPoint_characterization Q).mp hQ

/-- The estimated Q is the actual Q of the selected policy in the empirical MDP. -/
theorem qEstimator_eq_trajectory (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (s : State) (a : Action) :
    (empiricalModel M N hN data).trajectoryExpectedQ
      (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s a =
        qEstimator M N hN data s a := by
  exact (empiricalModel M N hN data).optimalGreedy_trajectoryQ s a

/-- The output policy simultaneously dominates all stationary randomized policies in the empirical MDP. -/
theorem policyEstimator_empirical_optimal (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (data : Samples State Action N) (π : StationaryPolicy State Action)
    (s : State) :
    (empiricalModel M N hN data).trajectoryExpectedValue π s ≤ valueEstimator M N hN data s := by
  exact (empiricalModel M N hN data).trajectoryValue_le_optimalGreedy π s

end StatisticalRL.ModelBasedPolicyLearning

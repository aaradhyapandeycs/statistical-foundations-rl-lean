import Formalization.ModelFree.QLearningSamplingDefinitions
import Formalization.ModelFree.QLearningIterateBounds
import Formalization.Generative.ModelBasedPolicyLearning

/-! Exact finite product experiment for synchronous generative Q-learning. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qSamplingStateMeasurable : MeasurableSpace State := ⊤
local instance qSamplingActionMeasurable : MeasurableSpace Action := ⊤

instance qSamplingLaw_probability (M : DiscountedMDP State Action) (T : ℕ) :
    IsProbabilityMeasure (qSamplingLaw M T) := by
  unfold qSamplingLaw
  infer_instance

/-- Each state/action/time coordinate has its actual MDP row law. -/
theorem qSamplingLaw_marginal (M : DiscountedMDP State Action) (T : ℕ)
    (s : State) (a : Action) (k : Fin T) :
    (qSamplingLaw M T).map (fun data ↦ data ((s,a),k)) = (M.transition s a).rowMeasure :=
  ModelBasedPolicyLearning.samplingLaw_marginal M T ((s,a),k)

/-- All sampled state/action/time coordinates are mutually independent. -/
theorem qSamplingLaw_independent (M : DiscountedMDP State Action) (T : ℕ) :
    iIndepFun (fun i (data : QSamples State Action T) ↦ data i) (qSamplingLaw M T) :=
  ModelBasedPolicyLearning.samplingLaw_independent M T

/-- Exact source update-time to sample-index correspondence. -/
theorem qSamplesExtend_succ (M : DiscountedMDP State Action) (T : ℕ)
    (data : QSamples State Action T) (t : ℕ) (ht : t < T) (s : State) (a : Action) :
    qSamplesExtend M T data (t + 1) s a = data ((s,a), ⟨t,ht⟩) := by
  simp [qSamplesExtend, show 0 < t + 1 ∧ t + 1 ≤ T by omega]

/-- The pathwise bound also controls actual optimal-trajectory Q error under
the genuine product experiment. -/
theorem qSampledIterate_error_ae (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T : ℕ) (Q₀ : State → Action → ℝ)
    (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon)
    (hη : ∀ k, 1 ≤ k → k ≤ T → 0 ≤ η k ∧ η k ≤ 1) :
    ∀ᵐ data ∂qSamplingLaw M T,
      ‖qSampledIterate M η T Q₀ data - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
        M.effectiveHorizon := by
  exact Filter.Eventually.of_forall fun data ↦
    qLearningIterate_optimalQ_error_norm_le M η (qSamplesExtend M T data) Q₀ h₀ T hη

end StatisticalRL.QLearning

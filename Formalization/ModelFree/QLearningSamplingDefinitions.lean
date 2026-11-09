import Formalization.ModelFree.QLearningIterateBounds
import Formalization.Generative.ModelBasedPolicyLearning

open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qSamplingDefsStateMeasurable : MeasurableSpace State := ⊤
local instance qSamplingDefsActionMeasurable : MeasurableSpace Action := ⊤

/-- Exactly T next-state draws per state/action, indexed from zero. -/
abbrev QSamples (State Action : Type*) (T : ℕ) := ModelBasedPolicyLearning.Samples State Action T

/-- The genuine product sampling law of the MDP transition rows. -/
noncomputable def qSamplingLaw (M : DiscountedMDP State Action) (T : ℕ) :
    Measure (QSamples State Action T) := ModelBasedPolicyLearning.samplingLaw M T

/-- Source iteration t+1 uses zero-indexed coordinate t; outside 1,…,T the
extension returns a fixed state, which is never queried by iterations ≤T. -/
noncomputable def qSamplesExtend (M : DiscountedMDP State Action) (T : ℕ)
    (data : QSamples State Action T) : ℕ → State → Action → State := fun t s a ↦
  if h : 0 < t ∧ t ≤ T then data ((s,a), ⟨t - 1, by omega⟩)
  else Classical.choice M.state_nonempty

/-- Actual Q-learning output after T synchronous updates. -/
noncomputable def qSampledIterate (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T : ℕ) (Q₀ : State → Action → ℝ) (data : QSamples State Action T) : State → Action → ℝ :=
  qLearningIterate M η (qSamplesExtend M T data) Q₀ T

/-- The auxiliary TD-type iteration of the under-estimation discussion
(`chapters/generative_model_model_free.tex:1871`): the same synchronous update and
next-state samples as `qLearningIterate`, but the next action is taken from the
deterministic policy `f` instead of maximizing over actions. -/
noncomputable def qPolicyEvaluationIterate (M : DiscountedMDP State Action)
    (f : State → Action) (η : ℕ → ℝ) (samples : ℕ → State → Action → State)
    (Q₀ : State → Action → ℝ) : ℕ → State → Action → ℝ
  | 0 => Q₀
  | t + 1 => fun s a ↦
      (1 - η (t + 1)) * qPolicyEvaluationIterate M f η samples Q₀ t s a +
        η (t + 1) * (M.reward s a + M.discount *
          qPolicyEvaluationIterate M f η samples Q₀ t (samples (t + 1) s a)
            (f (samples (t + 1) s a)))

/-- The auxiliary iterate after T updates on the same exact-T sample array as
`qSampledIterate`. -/
noncomputable def qPolicySampledIterate (M : DiscountedMDP State Action)
    (f : State → Action) (η : ℕ → ℝ) (T : ℕ) (Q₀ : State → Action → ℝ)
    (data : QSamples State Action T) : State → Action → ℝ :=
  qPolicyEvaluationIterate M f η (qSamplesExtend M T data) Q₀ T

end StatisticalRL.QLearning

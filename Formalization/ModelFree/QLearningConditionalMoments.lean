import Formalization.ModelFree.QLearningCausality
import Mathlib.Probability.ConditionalExpectation

/-! Definitions for Q-learning prefix conditional moments under the actual sampling law. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Action := ⊤

/-- Strict history before zero-based sample layer t. -/
noncomputable def qPastSigma (T t : ℕ) : MeasurableSpace (QSamples State Action T) :=
  MeasurableSpace.comap (qPastData (State := State) (Action := Action) T t) inferInstance

/-- Current value estimate, evaluated before layer t is sampled. -/
noncomputable def qValueBefore (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (Q₀ : State → Action → ℝ) (data : QSamples State Action T) : State → ℝ :=
  qLearningValue M (qLearningIterate M η (qSamplesExtend M T data) Q₀ t)

/-- Finite row mean of a state value vector. -/
noncomputable def qRowMean (M : DiscountedMDP State Action) (s : State) (a : Action)
    (v : State → ℝ) : ℝ := ∑ x, (M.transition s a).prob x * v x

/-- Actual row variance of a state value vector. -/
noncomputable def qRowVariance (M : DiscountedMDP State Action) (s : State) (a : Action)
    (v : State → ℝ) : ℝ := ∑ x, (M.transition s a).prob x * (v x - qRowMean M s a v)^2

/-- Predictable-value row fluctuation at the actual coordinate t. -/
noncomputable def qRowIncrement (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t < T) (Q₀ : State → Action → ℝ) (s : State) (a : Action)
    (data : QSamples State Action T) : ℝ :=
  let v := qValueBefore M η T t Q₀ data
  v (data ((s,a), ⟨t,ht⟩)) - qRowMean M s a v

end StatisticalRL.QLearning

import Formalization.ModelFree.QLearningPrefixFiltration
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! Indicator and finite-sum reduction for the actual Q-learning update. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Action := ⊤

/-- Indicator of the actual current-row sample attaining x. -/
noncomputable def qFreshIndicator (T t : ℕ) (ht : t < T) (s : State) (a : Action)
    (x : State) (data : QSamples State Action T) : ℝ := by
  classical
  exact if data ((s,a), ⟨t,ht⟩) = x then 1 else 0

/-- The predicted value can be expanded in mutually exclusive fresh-state indicators. -/
theorem qFresh_value_decomposition (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t < T) (Q₀ : State → Action → ℝ) (s : State) (a : Action)
    (data : QSamples State Action T) :
    qValueBefore M η T t Q₀ data (data ((s,a), ⟨t,ht⟩)) =
      ∑ x, qValueBefore M η T t Q₀ data x * qFreshIndicator T t ht s a x data := by
  classical
  simp [qFreshIndicator]

/- Conditional indicator and increment moments are established in QLearningConditionalIncrement. -/
end StatisticalRL.QLearning

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

/-- The squared centered increment has the analogous exact pathwise expansion. -/
theorem qFresh_increment_sq_decomposition (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t < T) (Q₀ : State → Action → ℝ) (s : State) (a : Action)
    (data : QSamples State Action T) :
    (qRowIncrement M η T t ht Q₀ s a data)^2 =
      ∑ x, (qValueBefore M η T t Q₀ data x -
        qRowMean M s a (qValueBefore M η T t Q₀ data))^2 *
        qFreshIndicator T t ht s a x data := by
  classical
  simp [qRowIncrement, qFreshIndicator]

/- Pending, without assuming either conclusion:
  * prove qPastSigma ≤ ambient and the current coordinate's generated sigma is
    independent of qPastSigma using qPast_indep_fresh, not just iterate independence;
  * apply condExp_indep_eq to qFreshIndicator and identify its integral using
    qSamplingLaw_marginal with (M.transition s a).prob x;
  * prove each predictable coefficient strongly measurable and all products
    integrable (the experiment is finite); use condExp_finset_sum and pull-out;
  * obtain centering and conditional second moment = qRowVariance, a.e. under
    qSamplingLaw M T. The proof concerns F_t, not priorIncrementSigma.
-/
end StatisticalRL.QLearning

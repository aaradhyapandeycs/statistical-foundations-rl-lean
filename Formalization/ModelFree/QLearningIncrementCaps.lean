import Formalization.Probability.Variance
import Formalization.ModelFree.QLearningNaturalHistory

/-! Deterministic Q-learning increment caps. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Action := ⊤

/-- Any sample from a distribution of values in [0,H] is within H of its mean. -/
theorem qRow_abs_centered_le (d : FiniteDistribution State) (v : State → ℝ)
    (H : ℝ) (hv : ∀ x, 0 ≤ v x ∧ v x ≤ H) (y : State) :
    |v y - d.expectation v| ≤ H := by
  have hlo : 0 ≤ d.expectation v := d.expectation_nonneg (fun x ↦ (hv x).1)
  have hhi : d.expectation v ≤ H := d.expectation_le_const (fun x ↦ (hv x).2)
  apply abs_le.mpr
  constructor <;> linarith [(hv y).1, (hv y).2]

/-- The true-row variance is at most H² for any value in [0,H]. -/
theorem qRowVariance_le_sq (M : DiscountedMDP State Action) (s : State) (a : Action)
    (v : State → ℝ) (H : ℝ) (hH : 0 ≤ H) (hv : ∀ x, 0 ≤ v x ∧ v x ≤ H) :
    qRowVariance M s a v ≤ H^2 := by
  change (M.transition s a).expectation
    (fun x ↦ (v x - (M.transition s a).expectation v)^2) ≤ H^2
  apply (M.transition s a).expectation_le_const
  intro x
  have hb := qRow_abs_centered_le (M.transition s a) v H hv x
  nlinarith [sq_nonneg (H - |v x - (M.transition s a).expectation v|),
    abs_nonneg (v x - (M.transition s a).expectation v), sq_abs (v x - (M.transition s a).expectation v)]

/-- Uniform pathwise bound for the zero-padded actual iterate-dependent increment. -/
theorem qPaddedIncrement_abs_le (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (Q₀ : State → Action → ℝ) (s : State) (a : Action)
    (h₀ : ∀ x b, 0 ≤ Q₀ x b ∧ Q₀ x b ≤ M.effectiveHorizon)
    (hη : ∀ k, 1 ≤ k → k ≤ T → 0 ≤ η k ∧ η k ≤ 1)
    (data : QSamples State Action T) :
    |qPaddedIncrement M η T Q₀ s a t data| ≤ M.effectiveHorizon := by
  classical
  by_cases ht : t < T
  · have hv : ∀ x, 0 ≤ qValueBefore M η T t Q₀ data x ∧
        qValueBefore M η T t Q₀ data x ≤ M.effectiveHorizon := by
      intro x
      exact qLearningIterate_value_bounds M η (qSamplesExtend M T data) Q₀ h₀ t
        (fun k hk hkt ↦ hη k hk (le_trans hkt (Nat.le_of_lt ht))) x
    simpa [qPaddedIncrement, ht, qRowIncrement, qRowMean, FiniteDistribution.expectation] using
      qRow_abs_centered_le (M.transition s a) (qValueBefore M η T t Q₀ data)
        M.effectiveHorizon hv (data ((s,a), ⟨t,ht⟩))
  · simpa [qPaddedIncrement, ht] using M.effectiveHorizon_nonneg

/-- Actual true-row variance of V_t has the same deterministic coarse cap. -/
theorem qValueBefore_rowVariance_le (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t < T) (Q₀ : State → Action → ℝ) (s : State) (a : Action)
    (h₀ : ∀ x b, 0 ≤ Q₀ x b ∧ Q₀ x b ≤ M.effectiveHorizon)
    (hη : ∀ k, 1 ≤ k → k ≤ T → 0 ≤ η k ∧ η k ≤ 1)
    (data : QSamples State Action T) :
    qRowVariance M s a (qValueBefore M η T t Q₀ data) ≤ M.effectiveHorizon^2 := by
  apply qRowVariance_le_sq M s a _ _ M.effectiveHorizon_nonneg
  intro x
  exact qLearningIterate_value_bounds M η (qSamplesExtend M T data) Q₀ h₀ t
    (fun k hk hkt ↦ hη k hk (le_trans hkt (Nat.le_of_lt ht))) x

/- A further conditional-expectation monotonicity proof must transfer this
pointwise variance cap through the smaller natural history; for t≥T the padded
increment is zero. Summing produces coarse deterministic T*H², not the sharp
source variance budget. The source's weighted V* fluctuation is a distinct
sequence and needs its own fixed-value and weight bounds. -/
end StatisticalRL.QLearning

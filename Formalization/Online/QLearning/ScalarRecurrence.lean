import Formalization.Online.QLearning.RateWeights

/-! algebraic prerequisite; the actual-table consumer is
separate and must establish its hypotheses by folding observed records. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- A generic source-schedule scalar recursion driven by its realized targets. -/
noncomputable def qLearningScalarRecurrence (H : ℕ) (initial : ℝ) (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => initial
  | n+1 => (1 - onlineQRate H (n+1)) * qLearningScalarRecurrence H initial f n +
      onlineQRate H (n+1) * f (n+1)

/-- The source's zero-index weight obeys the same scalar recursion. -/
lemma qLearningInitialWeight_succ (H n : ℕ) :
    onlineQRateWeight H (n+1) 0 =
      (1-onlineQRate H (n+1)) * onlineQRateWeight H n 0 := by
  classical
  simp only [onlineQRateWeight, ↓reduceIte]
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n+1)]
  ring

/-- Exact unrolling, including zero visits and the initial-value term. -/
theorem qLearningScalarRecurrence_eq_weighted (H n : ℕ) (initial : ℝ) (f : ℕ → ℝ) :
    qLearningScalarRecurrence H initial f n = onlineQRateWeight H n 0 * initial +
      ∑ i ∈ Finset.Icc 1 n, onlineQRateWeight H n i * f i := by
  classical
  induction n with
  | zero => simp [qLearningScalarRecurrence, onlineQRateWeight]
  | succ n ih =>
      rw [qLearningScalarRecurrence, ih, qLearningInitialWeight_succ,
        onlineQRateWeight_sum_succ]
      ring

end StatisticalRL.OnlineRL

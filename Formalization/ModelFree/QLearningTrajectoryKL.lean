import Formalization.MDP.Basic
import Formalization.Generative.GenerativeLowerBoundFiniteKLDataProcessing

/-! One-step KL chain rule for actual finite Markov transition laws. -/
open scoped BigOperators
namespace StatisticalRL.QLearning

variable {State : Type*} [Fintype State]

/-- Actual joint law of the current state and its next state when the current
state has law `μ` and the transition row at `x` is `K x`. -/
def qMarkovStepLaw (μ : FiniteDistribution State)
    (K : State → FiniteDistribution State) : FiniteDistribution (State × State) where
  prob xy := μ.prob xy.1 * (K xy.1).prob xy.2
  prob_nonneg xy := mul_nonneg (μ.prob_nonneg _) ((K xy.1).prob_nonneg _)
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (K _).sum_prob, mul_one]
    exact μ.sum_prob

/-- One-step finite KL chain rule. It is zero-support-safe: absolute
continuity is expressed as support inclusion for the initial law and every
conditional row. This identity is the reusable induction step for Markov
trajectory KL. -/
theorem qMarkovStep_finiteKL_chainRule
    (μ μ' : FiniteDistribution State)
    (K K' : State → FiniteDistribution State)
    (hμ : ∀ x, μ'.prob x ≠ 0 → μ.prob x ≠ 0)
    (hK : ∀ x y, (K' x).prob y ≠ 0 → (K x).prob y ≠ 0) :
    StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun xy ↦ (qMarkovStepLaw μ' K').prob xy)
        (fun xy ↦ (qMarkovStepLaw μ K).prob xy) =
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
          (fun x ↦ μ'.prob x) (fun x ↦ μ.prob x) +
        μ'.expectation (fun x ↦
          StatisticalRL.GenerativeLowerBound.finiteKLExpression
            (fun y ↦ (K' x).prob y) (fun y ↦ (K x).prob y)) := by
  classical
  have hlog_factor (x y : State)
      (ha : μ'.prob x ≠ 0) (hc : (K' x).prob y ≠ 0) :
      Real.log
          ((μ'.prob x * (K' x).prob y) / (μ.prob x * (K x).prob y)) =
        Real.log (μ'.prob x / μ.prob x) +
          Real.log ((K' x).prob y / (K x).prob y) := by
    have haPos : 0 < μ'.prob x := lt_of_le_of_ne (μ'.prob_nonneg x) (Ne.symm ha)
    have hcPos : 0 < (K' x).prob y :=
      lt_of_le_of_ne ((K' x).prob_nonneg y) (Ne.symm hc)
    have hb : 0 < μ.prob x :=
      lt_of_le_of_ne (μ.prob_nonneg x) (Ne.symm (hμ x ha))
    have hd : 0 < (K x).prob y :=
      lt_of_le_of_ne ((K x).prob_nonneg y) (Ne.symm (hK x y hc))
    have hmul :
        (μ'.prob x * (K' x).prob y) / (μ.prob x * (K x).prob y) =
          (μ'.prob x / μ.prob x) * ((K' x).prob y / (K x).prob y) := by
      field_simp [ne_of_gt hb, ne_of_gt hd]
    rw [hmul, Real.log_mul (ne_of_gt (div_pos haPos hb))
      (ne_of_gt (div_pos hcPos hd)), Real.log_div (ne_of_gt haPos) (ne_of_gt hb),
      Real.log_div (ne_of_gt hcPos) (ne_of_gt hd)]

  have hpoint (x y : State) :
      (μ'.prob x * (K' x).prob y) *
          Real.log ((μ'.prob x * (K' x).prob y) /
            (μ.prob x * (K x).prob y)) =
        (μ'.prob x * Real.log (μ'.prob x / μ.prob x)) * (K' x).prob y +
          μ'.prob x * ((K' x).prob y *
            Real.log ((K' x).prob y / (K x).prob y)) := by
    by_cases ha : μ'.prob x = 0
    · simp [ha]
    by_cases hc : (K' x).prob y = 0
    · simp [hc]
    rw [hlog_factor x y ha hc]
    ring

  have hsum :
      (∑ x, ∑ y, (μ'.prob x * (K' x).prob y) *
        Real.log ((μ'.prob x * (K' x).prob y) /
          (μ.prob x * (K x).prob y))) =
        (∑ x, μ'.prob x * Real.log (μ'.prob x / μ.prob x)) +
          ∑ x, μ'.prob x *
            (∑ y, (K' x).prob y * Real.log ((K' x).prob y / (K x).prob y)) := by
    calc
      _ = ∑ x, ∑ y,
          ((μ'.prob x * Real.log (μ'.prob x / μ.prob x)) * (K' x).prob y +
            μ'.prob x * ((K' x).prob y *
              Real.log ((K' x).prob y / (K x).prob y))) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact hpoint x y
      _ = _ := by
        simp_rw [Finset.sum_add_distrib]
        congr 1
        · simp_rw [← Finset.mul_sum, (K' _).sum_prob, mul_one]
        · simp_rw [← Finset.mul_sum]

  change (∑ xy : State × State,
      (μ'.prob xy.1 * (K' xy.1).prob xy.2) *
        Real.log ((μ'.prob xy.1 * (K' xy.1).prob xy.2) /
          (μ.prob xy.1 * (K xy.1).prob xy.2))) =
    (∑ x : State, μ'.prob x * Real.log (μ'.prob x / μ.prob x)) +
      ∑ x : State, μ'.prob x *
        (∑ y : State, (K' x).prob y *
          Real.log ((K' x).prob y / (K x).prob y))
  rw [Fintype.sum_prod_type]
  exact hsum

end StatisticalRL.QLearning

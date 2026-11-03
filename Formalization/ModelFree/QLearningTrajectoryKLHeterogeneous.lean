import Formalization.MDP.Basic
import Formalization.Generative.GenerativeLowerBoundFiniteKLDataProcessing

/-! Finite heterogeneous joint-law KL chain rule. -/
open scoped BigOperators
namespace StatisticalRL.QLearning

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Joint law obtained by sampling `x` from `μ`, then `y` from row `K x`. -/
def qConditionalJointLaw (μ : FiniteDistribution X)
    (K : X → FiniteDistribution Y) : FiniteDistribution (X × Y) where
  prob xy := μ.prob xy.1 * (K xy.1).prob xy.2
  prob_nonneg xy := mul_nonneg (μ.prob_nonneg _) ((K xy.1).prob_nonneg _)
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (K _).sum_prob, mul_one]
    exact μ.sum_prob

/-- Heterogeneous finite KL chain rule. The support assumptions are
likelihood-support inclusions, so neither the marginal nor the conditional
rows need full support. -/
theorem qConditionalJoint_finiteKL_chainRule
    (μ μ' : FiniteDistribution X)
    (K K' : X → FiniteDistribution Y)
    (hμ : ∀ x, μ'.prob x ≠ 0 → μ.prob x ≠ 0)
    (hK : ∀ x y, (K' x).prob y ≠ 0 → (K x).prob y ≠ 0) :
    StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun xy ↦ (qConditionalJointLaw μ' K').prob xy)
        (fun xy ↦ (qConditionalJointLaw μ K).prob xy) =
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
          (fun x ↦ μ'.prob x) (fun x ↦ μ.prob x) +
        μ'.expectation (fun x ↦
          StatisticalRL.GenerativeLowerBound.finiteKLExpression
            (fun y ↦ (K' x).prob y) (fun y ↦ (K x).prob y)) := by
  classical
  have hlog_factor (x : X) (y : Y)
      (ha : μ'.prob x ≠ 0) (hc : (K' x).prob y ≠ 0) :
      Real.log ((μ'.prob x * (K' x).prob y) /
        (μ.prob x * (K x).prob y)) =
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

  have hpoint (x : X) (y : Y) :
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
      (∑ x : X, ∑ y : Y, (μ'.prob x * (K' x).prob y) *
        Real.log ((μ'.prob x * (K' x).prob y) /
          (μ.prob x * (K x).prob y))) =
        (∑ x : X, μ'.prob x * Real.log (μ'.prob x / μ.prob x)) +
          ∑ x : X, μ'.prob x *
            (∑ y : Y, (K' x).prob y *
              Real.log ((K' x).prob y / (K x).prob y)) := by
    calc
      _ = ∑ x : X, ∑ y : Y,
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

  change (∑ xy : X × Y,
      (μ'.prob xy.1 * (K' xy.1).prob xy.2) *
        Real.log ((μ'.prob xy.1 * (K' xy.1).prob xy.2) /
          (μ.prob xy.1 * (K xy.1).prob xy.2))) =
    (∑ x : X, μ'.prob x * Real.log (μ'.prob x / μ.prob x)) +
      ∑ x : X, μ'.prob x *
        (∑ y : Y, (K' x).prob y * Real.log ((K' x).prob y / (K x).prob y))
  rw [Fintype.sum_prod_type]
  exact hsum

/-- With a common marginal, the marginal KL term vanishes. This is useful
when a common policy draws an action before the model-dependent suffix. -/
theorem qConditionalJoint_commonMarginal_chainRule
    (μ : FiniteDistribution X) (K K' : X → FiniteDistribution Y)
    (hK : ∀ x y, (K' x).prob y ≠ 0 → (K x).prob y ≠ 0) :
    StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun xy ↦ (qConditionalJointLaw μ K').prob xy)
        (fun xy ↦ (qConditionalJointLaw μ K).prob xy) =
      μ.expectation (fun x ↦
        StatisticalRL.GenerativeLowerBound.finiteKLExpression
          (fun y ↦ (K' x).prob y) (fun y ↦ (K x).prob y)) := by
  have hself : StatisticalRL.GenerativeLowerBound.finiteKLExpression
      (fun x ↦ μ.prob x) (fun x ↦ μ.prob x) = 0 := by
    unfold StatisticalRL.GenerativeLowerBound.finiteKLExpression
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hzero : μ.prob x = 0
    · simp [hzero]
    · have hpos : 0 < μ.prob x :=
        lt_of_le_of_ne (μ.prob_nonneg x) (Ne.symm hzero)
      simp [div_self (ne_of_gt hpos)]
  rw [qConditionalJoint_finiteKL_chainRule μ μ K K'
    (fun _ h ↦ h) hK, hself, zero_add]

end StatisticalRL.QLearning

import Formalization.ModelFree.QLearningChiSourceParameters

/-! Source simplified residual upper bound and
actual-comparator noise-radius domination. No stochastic event is assumed as
a theorem conclusion; deterministic radius domination is proved separately. -/
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Centered span controls actual finite row variance despite a reward shift. -/
theorem qChi_variance_le_centered_span_sq (p : FiniteDistribution State) (v : State → ℝ)
    (H : ℝ) (hH : 0 ≤ H) (hv : ∀ x, |v x - p.expectation v| ≤ H) :
    p.variance v ≤ H ^ 2 := by
  rw [p.variance_eq_expectation_centered_sq]
  calc
    _ ≤ p.expectation (fun _ ↦ H ^ 2) := by
      apply p.expectation_mono
      intro x
      have hh := hv x
      nlinarith [sq_abs (v x - p.expectation v), abs_nonneg (v x - p.expectation v)]
    _ = _ := p.expectation_const _

/-- Exact scalar simplification used in the source upper residual bound. -/
theorem qChi_discounted_sqrt_variance_le (γ ρ H v : ℝ)
    (_hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hρ : 0 ≤ ρ) (hH : 0 ≤ H)
    (hv : 0 ≤ v) (hvH : v ≤ H ^ 2) :
    γ * Real.sqrt (ρ * v) ≤ Real.sqrt ρ * H := by
  have hs : Real.sqrt v ≤ H := by
    nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
  rw [Real.sqrt_mul hρ]
  have h1 := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg ρ)
  have h2 := mul_le_mul_of_nonneg_right hγ1 (mul_nonneg (Real.sqrt_nonneg ρ) (Real.sqrt_nonneg v))
  nlinarith

/-- Both actual comparator residuals have the source common simplified upper
bound, derived from their true shifted range rather than an absolute bound. -/
theorem qChi_actualComparatorResidual_upper (M : DiscountedMDP State Action)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (s : State) (a : Action) :
    qComparatorResidualPlus M (qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ) s a ≤
        (2 * ρ + Real.sqrt ρ) * M.effectiveHorizon ∧
    qComparatorResidualMinus M (qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ) s a ≤
        (2 * ρ + Real.sqrt ρ) * M.effectiveHorizon := by
  let Qp := qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ
  let Qm := qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ
  have hsp := fun x y ↦ (qRobustComparator_value_pairwise_span M ρ (2 * ρ * M.effectiveHorizon) hρ x y).1
  have hsm := fun x y ↦ (qRobustComparator_value_pairwise_span M ρ (2 * ρ * M.effectiveHorizon) hρ x y).2
  have hvp := qChi_variance_le_centered_span_sq (M.transition s a) (qLearningValue M Qp)
    M.effectiveHorizon M.effectiveHorizon_nonneg
    (qChi_abs_centered_le_of_pairwise _ _ _ hsp)
  have hvm := qChi_variance_le_centered_span_sq (M.transition s a) (qLearningValue M Qm)
    M.effectiveHorizon M.effectiveHorizon_nonneg
    (qChi_abs_centered_le_of_pairwise _ _ _ hsm)
  have hbp := (qChi_upperResidual_bounds M ρ hρ Qp
    (qRobustPlusFixedPoint_spec M ρ _ hρ) hsp s a).2
  have hbm := (qChi_lowerResidual_bounds M ρ hρ Qm
    (qRobustMinusFixedPoint_spec M ρ _ hρ) hsm s a).2
  have hxp := qChi_discounted_sqrt_variance_le M.discount ρ M.effectiveHorizon _ M.discount_nonneg
    M.discount_lt_one.le hρ M.effectiveHorizon_nonneg ((M.transition s a).variance_nonneg _) hvp
  have hxm := qChi_discounted_sqrt_variance_le M.discount ρ M.effectiveHorizon _ M.discount_nonneg
    M.discount_lt_one.le hρ M.effectiveHorizon_nonneg ((M.transition s a).variance_nonneg _) hvm
  constructor <;> change _ ≤ _ <;> dsimp [Qp, Qm] at * <;> nlinarith

/-- The source stochastic radius is deterministically dominated for both
actual comparators. Proving the all-row/time radius event remains separate. -/
theorem qChi_actualComparatorResidual_absorbs_radius (M : DiscountedMDP State Action)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (s : State) (a : Action) :
    (M.discount * Real.sqrt (ρ * (M.transition s a).variance
        (qLearningValue M (qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ))) +
      (M.discount / 6) * ρ * M.effectiveHorizon ≤ qComparatorResidualPlus M
        (qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ) s a) ∧
    (M.discount * Real.sqrt (ρ * (M.transition s a).variance
        (qLearningValue M (qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ))) +
      (M.discount / 6) * ρ * M.effectiveHorizon ≤ qComparatorResidualMinus M
        (qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ) s a) := by
  have hl := qChi_actualComparatorResidual_lower M ρ hρ s a
  have hs := qChi_residual_slack_dominates M.discount ρ M.effectiveHorizon M.discount_nonneg
    M.discount_lt_one.le hρ M.effectiveHorizon_nonneg
  exact ⟨by linarith [hl.1], by linarith [hl.2]⟩

end StatisticalRL.QLearning

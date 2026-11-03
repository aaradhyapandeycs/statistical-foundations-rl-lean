import Formalization.ModelFree.QLearningChiComparison
import Formalization.ModelFree.QLearningRobustRange

/-! Deterministic use of support comparison in source
robust-Q residual analysis. No fluctuation/probability conclusion is assumed. -/
namespace StatisticalRL.QLearning
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Source eq:Q-comparison-parameters, with its c2 denominator retained. -/
noncomputable def qChiSourceRateEnvelope (γ c₂ : ℝ) (T : ℕ) : ℝ :=
  min 1 (2 * Real.log (T : ℝ) ^ 3 / (c₂ * (1 - γ) * T))

/-- Source eq:defn-rho-b-model-free-proof. -/
noncomputable def qChiSourceRadius (ηbar δ : ℝ) (S A T : ℕ) : ℝ :=
  8 * ηbar * Real.log (4 * (S : ℝ) * A * T / δ)

noncomputable def qChiSourceRewardShift (γ ρ : ℝ) : ℝ := 2 * ρ / (1 - γ)

/-- The actual upper robust fixed-point residual absorbs the source's
standard-deviation scale plus its deterministic slack. A pairwise span is a
bounded-helper premise, to be discharged by the actual comparator range proof. -/
theorem qChi_upperResidual_bounds (M : DiscountedMDP State Action) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (Q : State → Action → ℝ)
    (hQ : qRobustBellmanPlus M ρ (2 * ρ * M.effectiveHorizon) Q = Q)
    (hspan : ∀ x y, |qLearningValue M Q x - qLearningValue M Q y| ≤ M.effectiveHorizon)
    (s : State) (a : Action) :
    M.discount * Real.sqrt (ρ * (M.transition s a).variance (qLearningValue M Q)) +
        (2 - M.discount) * ρ * M.effectiveHorizon ≤
      qComparatorResidualPlus M Q s a ∧
    qComparatorResidualPlus M Q s a ≤ 2 * ρ * M.effectiveHorizon +
        M.discount * Real.sqrt (ρ * (M.transition s a).variance (qLearningValue M Q)) := by
  let v := qLearningValue M Q
  have hc := qChi_abs_centered_le_of_pairwise (M.transition s a) v M.effectiveHorizon hspan
  have hl := qRobustExpectations_sSup_sub_ge_of_centered_span (M.transition s a) v
    M.effectiveHorizon ρ (by
      unfold DiscountedMDP.effectiveHorizon
      exact one_div_pos.mpr (sub_pos.mpr M.discount_lt_one)) hρ hc
  have hu := qRobustExpectations_sSup_sub_le (M.transition s a) ρ hρ v
  have he := qComparatorResidualPlus_eq M ρ (2 * ρ * M.effectiveHorizon) Q hQ s a
  have hgl := mul_le_mul_of_nonneg_left hl M.discount_nonneg
  have hgu := mul_le_mul_of_nonneg_left hu M.discount_nonneg
  constructor <;> dsimp [v] at * <;> nlinarith

/-- The lower robust residual is derived with its own sign convention. -/
theorem qChi_lowerResidual_bounds (M : DiscountedMDP State Action) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (Q : State → Action → ℝ)
    (hQ : qRobustBellmanMinus M ρ (2 * ρ * M.effectiveHorizon) Q = Q)
    (hspan : ∀ x y, |qLearningValue M Q x - qLearningValue M Q y| ≤ M.effectiveHorizon)
    (s : State) (a : Action) :
    M.discount * Real.sqrt (ρ * (M.transition s a).variance (qLearningValue M Q)) +
        (2 - M.discount) * ρ * M.effectiveHorizon ≤ qComparatorResidualMinus M Q s a ∧
    qComparatorResidualMinus M Q s a ≤ 2 * ρ * M.effectiveHorizon +
        M.discount * Real.sqrt (ρ * (M.transition s a).variance (qLearningValue M Q)) := by
  let v := qLearningValue M Q
  have hc : ∀ x, |-v x - (M.transition s a).expectation (fun x ↦ -v x)| ≤ M.effectiveHorizon := by
    have hp := qChi_abs_centered_le_of_pairwise (M.transition s a) v M.effectiveHorizon hspan
    intro x
    rw [qChi_expectation_neg]
    have he : -v x - -(M.transition s a).expectation v = -(v x - (M.transition s a).expectation v) := by ring
    rw [he, abs_neg]
    exact hp x
  have hH : 0 < M.effectiveHorizon := by
    unfold DiscountedMDP.effectiveHorizon
    exact one_div_pos.mpr (sub_pos.mpr M.discount_lt_one)
  have hl := qRobustExpectations_sSup_sub_ge_of_centered_span (M.transition s a)
    (fun x ↦ -v x) M.effectiveHorizon ρ hH hρ hc
  have hu := qRobustExpectations_sSup_sub_le (M.transition s a) ρ hρ (fun x ↦ -v x)
  rw [qChi_variance_neg, qChi_expectation_neg, qChi_sSup_neg_eq_neg_sInf _ ρ hρ v] at hl hu
  have he := qComparatorResidualMinus_eq M ρ (2 * ρ * M.effectiveHorizon) Q hQ s a
  have hgl := mul_le_mul_of_nonneg_left hl M.discount_nonneg
  have hgu := mul_le_mul_of_nonneg_left hu M.discount_nonneg
  constructor <;> dsimp [v] at * <;> nlinarith

/-- Actual deterministic comparator consumption: their spans are proved by
shifted true-MDP optimal values, and are not assumed in this corollary. -/
theorem qChi_actualComparatorResidual_lower (M : DiscountedMDP State Action)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (s : State) (a : Action) :
    (M.discount * Real.sqrt (ρ * (M.transition s a).variance
        (qLearningValue M (qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ))) +
      (2 - M.discount) * ρ * M.effectiveHorizon ≤ qComparatorResidualPlus M
        (qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ) s a) ∧
    (M.discount * Real.sqrt (ρ * (M.transition s a).variance
        (qLearningValue M (qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ))) +
      (2 - M.discount) * ρ * M.effectiveHorizon ≤ qComparatorResidualMinus M
        (qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ) s a) := by
  have hp := qChi_upperResidual_bounds M ρ hρ _
    (qRobustPlusFixedPoint_spec M ρ (2 * ρ * M.effectiveHorizon) hρ)
    (fun x y ↦ (qRobustComparator_value_pairwise_span M ρ (2 * ρ * M.effectiveHorizon) hρ x y).1) s a
  have hm := qChi_lowerResidual_bounds M ρ hρ _
    (qRobustMinusFixedPoint_spec M ρ (2 * ρ * M.effectiveHorizon) hρ)
    (fun x y ↦ (qRobustComparator_value_pairwise_span M ρ (2 * ρ * M.effectiveHorizon) hρ x y).2) s a
  exact ⟨hp.1, hm.1⟩

/-- Numeric slack comparison used immediately after the source residual bound. -/
theorem qChi_residual_slack_dominates (γ ρ H : ℝ)
    (_hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hρ : 0 ≤ ρ) (hH : 0 ≤ H) :
    (γ / 6) * ρ * H ≤ (2 - γ) * ρ * H := by
  have hh : γ / 6 ≤ 2 - γ := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hρ) hH

end StatisticalRL.QLearning

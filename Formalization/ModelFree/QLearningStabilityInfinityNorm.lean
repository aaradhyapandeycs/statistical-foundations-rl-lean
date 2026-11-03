import Formalization.ModelFree.QLearningStoppedPrefixPinskerStabilityBridge
import Formalization.ModelFree.QLearningChiComparison

/-! Source Q-comparison-facts support bounds and actual optimal trajectory-Q infinity-norm stability. -/
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Actual own-model optimal trajectory-Q stability in the finite Pi norm.
The nonnegative-radius endpoint is included beyond the printed positive domain. -/
theorem qChiBall_optimal_trajectoryQ_norm_stability
    (M M' : DiscountedMDP State Action)
    (hr : M'.reward = M.reward) (hγ : M'.discount = M.discount)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hballs : ∀ s a, M'.transition s a ∈ qChiBall (M.transition s a) ρ) :
    ‖M'.trajectoryExpectedQ M'.optimalGreedyPolicy -
      M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
      Real.sqrt (ρ * M.discount / (2 * (1 - M.discount) ^ 3)) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro s
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro a
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    qStopped_optimal_stability_of_chiBall_rows M M' hr hγ ρ hρ hballs s a

/-- Source Lemma 4.10(ii), with its printed positive radius and actual own-model
optimal forced-action trajectory values. Only same reward/discount and actual
supported chi-square-ball membership are assumed. -/
theorem qComparisonFacts_stability_source
    (M M' : DiscountedMDP State Action) (ρ : ℝ) (hρ : 0 < ρ)
    (hr : M'.reward = M.reward) (hγ : M'.discount = M.discount)
    (hballs : ∀ s a, M'.transition s a ∈ qChiBall (M.transition s a) ρ) :
    ‖M'.trajectoryExpectedQ M'.optimalGreedyPolicy -
      M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
      Real.sqrt (ρ * M.discount / (2 * (1 - M.discount) ^ 3)) :=
  qChiBall_optimal_trajectoryQ_norm_stability M M' hr hγ ρ hρ.le hballs

/-- Source part (i): both supremum and infimum deviations with the literal
rho/(1−gamma) correction and actual finite max-minus-min span. This wrapper
uses the already production-proved support comparison, not a centered-span
hypothesis or a location bound on v. -/
theorem qComparisonFacts_support_source [Nonempty State]
    (p : FiniteDistribution State) (γ ρ : ℝ) (hγ1 : γ < 1) (hρ : 0 < ρ)
    (v : State → ℝ) (hspan : qChiValueSpan v ≤ 1 / (1 - γ)) :
    (Real.sqrt (ρ * p.variance v) - ρ / (1 - γ) ≤
        sSup (qRobustExpectations p ρ v) - p.expectation v ∧
      sSup (qRobustExpectations p ρ v) - p.expectation v ≤ Real.sqrt (ρ * p.variance v)) ∧
    (Real.sqrt (ρ * p.variance v) - ρ / (1 - γ) ≤
        p.expectation v - sInf (qRobustExpectations p ρ v) ∧
      p.expectation v - sInf (qRobustExpectations p ρ v) ≤ Real.sqrt (ρ * p.variance v)) := by
  have hH : 0 < 1 / (1 - γ) := div_pos (by norm_num) (sub_pos.mpr hγ1)
  simpa only [one_div, div_eq_mul_inv, one_mul] using
    qChi_support_comparison p ρ (1 / (1 - γ)) hρ.le hH v hspan

end StatisticalRL.QLearning

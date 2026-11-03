import Formalization.ModelFree.QLearningRobustRange
import Formalization.MDP.OptimalTrajectoryValue
import Formalization.ModelFree.QLearningChiKL

/-! actual selected-model and reward-shift reduction
for source comparator closeness. No KL/Pinsker stability estimate is assumed. -/
open MeasureTheory
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qComparatorDistanceStateMeasurable : MeasurableSpace State := ⊤

/-- The actual selected rows satisfy the support-aware source ball, with
unchanged known rewards and discount. These are proved construction facts. -/
theorem qComparator_selectedModel_specs (M : DiscountedMDP State Action)
    (ρ b : ℝ) (hρ : 0 ≤ ρ) :
    ((∀ s a, (qRobustPlusModel M ρ b hρ).transition s a ∈ qChiBall (M.transition s a) ρ) ∧
      (qRobustPlusModel M ρ b hρ).reward = M.reward ∧
      (qRobustPlusModel M ρ b hρ).discount = M.discount) ∧
    ((∀ s a, (qRobustMinusModel M ρ b hρ).transition s a ∈ qChiBall (M.transition s a) ρ) ∧
      (qRobustMinusModel M ρ b hρ).reward = M.reward ∧
      (qRobustMinusModel M ρ b hρ).discount = M.discount) := by
  exact ⟨⟨fun s a ↦ (qRobustPlusOptimizer_spec M ρ b hρ s a).1, rfl, rfl⟩,
    ⟨fun s a ↦ (qRobustMinusOptimizer_spec M ρ b hρ s a).1, rfl, rfl⟩⟩

/-- Actual selected rows have finite measure KL at most rho, including zero
nominal atoms. This supplies a genuine input to the separate trajectory chain,
not a stability conclusion or an assumed absolute-continuity hypothesis. -/
theorem qComparator_selectedModel_rowKL (M : DiscountedMDP State Action)
    (ρ b : ℝ) (hρ : 0 ≤ ρ) :
    (∀ s a, ((qRobustPlusModel M ρ b hρ).transition s a).rowMeasure ≪ (M.transition s a).rowMeasure ∧
      InformationTheory.klDiv ((qRobustPlusModel M ρ b hρ).transition s a).rowMeasure
        (M.transition s a).rowMeasure ≠ ⊤ ∧
      (InformationTheory.klDiv ((qRobustPlusModel M ρ b hρ).transition s a).rowMeasure
        (M.transition s a).rowMeasure).toReal ≤ ρ) ∧
    (∀ s a, ((qRobustMinusModel M ρ b hρ).transition s a).rowMeasure ≪ (M.transition s a).rowMeasure ∧
      InformationTheory.klDiv ((qRobustMinusModel M ρ b hρ).transition s a).rowMeasure
        (M.transition s a).rowMeasure ≠ ⊤ ∧
      (InformationTheory.klDiv ((qRobustMinusModel M ρ b hρ).transition s a).rowMeasure
        (M.transition s a).rowMeasure).toReal ≤ ρ) := by
  have hs := qComparator_selectedModel_specs M ρ b hρ
  constructor
  · intro s a
    have hp := hs.1.1 s a
    have hac := qChi_rowMeasure_absolutelyContinuous (M.transition s a)
      ((qRobustPlusModel M ρ b hρ).transition s a) hp.1
    exact ⟨hac, StatisticalRL.GenerativeLowerBound.finite_klDiv_ne_top_of_ac _ _ hac,
      (qChi_rowKL_le _ _ hp.1).trans hp.2⟩
  · intro s a
    have hp := hs.2.1 s a
    have hac := qChi_rowMeasure_absolutelyContinuous (M.transition s a)
      ((qRobustMinusModel M ρ b hρ).transition s a) hp.1
    exact ⟨hac, StatisticalRL.GenerativeLowerBound.finite_klDiv_ne_top_of_ac _ _ hac,
      (qChi_rowKL_le _ _ hp.1).trans hp.2⟩

/-- Both shifted comparator identities hold for actual optimal forced-action
trajectory Q in the selected models, not merely Bellman fixed-point symbols. -/
theorem qComparator_shifted_optimalTrajectoryQ (M : DiscountedMDP State Action)
    (ρ b : ℝ) (hρ : 0 ≤ ρ) (s : State) (a : Action) :
    (qRobustPlusFixedPoint M ρ b hρ s a - b/(1-M.discount) =
      (qRobustPlusModel M ρ b hρ).trajectoryExpectedQ
        (qRobustPlusModel M ρ b hρ).optimalGreedyPolicy s a) ∧
    (qRobustMinusFixedPoint M ρ b hρ s a + b/(1-M.discount) =
      (qRobustMinusModel M ρ b hρ).trajectoryExpectedQ
        (qRobustMinusModel M ρ b hρ).optimalGreedyPolicy s a) := by
  have hs := qRobustComparator_shifted_fixedPoints M ρ b hρ
  rw [(qRobustPlusModel M ρ b hρ).optimalGreedy_trajectoryQ,
    (qRobustMinusModel M ρ b hρ).optimalGreedy_trajectoryQ]
  exact ⟨congrFun (congrFun hs.1 s) a, congrFun (congrFun hs.2 s) a⟩

/-- Exact pathwise model-distance decomposition for both residual signs. -/
theorem qComparator_distance_decomposition (M : DiscountedMDP State Action)
    (ρ b : ℝ) (hρ : 0 ≤ ρ) (s : State) (a : Action) :
    (qRobustPlusFixedPoint M ρ b hρ s a - M.trajectoryExpectedQ M.optimalGreedyPolicy s a =
      ((qRobustPlusModel M ρ b hρ).trajectoryExpectedQ
        (qRobustPlusModel M ρ b hρ).optimalGreedyPolicy s a -
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a) + b/(1-M.discount)) ∧
    (qRobustMinusFixedPoint M ρ b hρ s a - M.trajectoryExpectedQ M.optimalGreedyPolicy s a =
      ((qRobustMinusModel M ρ b hρ).trajectoryExpectedQ
        (qRobustMinusModel M ρ b hρ).optimalGreedyPolicy s a -
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a) - b/(1-M.discount)) := by
  have hs := qComparator_shifted_optimalTrajectoryQ M ρ b hρ s a
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- Actual source b=2rho/h yields exactly the source additive 2rho/h² cost.
The remaining terms are actual selected-model distances, with no unproved
sqrt stability bound smuggled into the assumptions. -/
theorem qComparator_source_distance_reduction (M : DiscountedMDP State Action)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (s : State) (a : Action) :
    (|qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
      |(qRobustPlusModel M ρ (2*ρ*M.effectiveHorizon) hρ).trajectoryExpectedQ
        (qRobustPlusModel M ρ (2*ρ*M.effectiveHorizon) hρ).optimalGreedyPolicy s a -
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a| + 2*ρ/(1-M.discount)^2) ∧
    (|qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
      |(qRobustMinusModel M ρ (2*ρ*M.effectiveHorizon) hρ).trajectoryExpectedQ
        (qRobustMinusModel M ρ (2*ρ*M.effectiveHorizon) hρ).optimalGreedyPolicy s a -
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a| + 2*ρ/(1-M.discount)^2) := by
  have hs := qComparator_distance_decomposition M ρ (2*ρ*M.effectiveHorizon) hρ s a
  have hgap : 1-M.discount ≠ 0 := ne_of_gt (sub_pos.mpr M.discount_lt_one)
  have hshift : (2*ρ*M.effectiveHorizon)/(1-M.discount) = 2*ρ/(1-M.discount)^2 := by
    unfold DiscountedMDP.effectiveHorizon
    field_simp
  have hshift0 : 0 ≤ 2*ρ/(1-M.discount)^2 := div_nonneg (mul_nonneg (by norm_num) hρ) (sq_nonneg _)
  constructor
  · rw [hs.1, hshift]
    exact (abs_add_le _ _).trans_eq (by rw [abs_of_nonneg hshift0])
  · rw [hs.2, hshift]
    have ht := abs_add_le
      ((qRobustMinusModel M ρ (2*ρ*M.effectiveHorizon) hρ).trajectoryExpectedQ
        (qRobustMinusModel M ρ (2*ρ*M.effectiveHorizon) hρ).optimalGreedyPolicy s a -
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a) (-(2*ρ/(1-M.discount)^2))
    rw [abs_neg, abs_of_nonneg hshift0] at ht
    simpa only [sub_eq_add_neg] using ht

/-- Finite Pi-norm lifting of the actual pointwise distance reduction. -/
theorem qComparator_norm_le_of_pointwise (F G : State → Action → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ s a, |F s a| ≤ |G s a| + C) : ‖F‖ ≤ ‖G‖ + C := by
  have hR : 0 ≤ ‖G‖+C := add_nonneg (norm_nonneg _) hC
  apply (pi_norm_le_iff_of_nonneg hR).2
  intro s
  apply (pi_norm_le_iff_of_nonneg hR).2
  intro a
  have hg : |G s a| ≤ ‖G‖ := by
    have hh := (norm_le_pi_norm (G s) a).trans (norm_le_pi_norm G s)
    simpa only [Real.norm_eq_abs] using hh
  simpa only [Real.norm_eq_abs] using (h s a).trans (add_le_add hg (le_refl C))

/-- Exact source supremum-norm reduction to actual selected-model trajectory
Q distances plus 2rho/h²; no sharp stability bound is a premise. -/
theorem qComparator_source_norm_distance_reduction (M : DiscountedMDP State Action)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (‖qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
      ‖(qRobustPlusModel M ρ (2*ρ*M.effectiveHorizon) hρ).trajectoryExpectedQ
        (qRobustPlusModel M ρ (2*ρ*M.effectiveHorizon) hρ).optimalGreedyPolicy -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖ + 2*ρ/(1-M.discount)^2) ∧
    (‖qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
      ‖(qRobustMinusModel M ρ (2*ρ*M.effectiveHorizon) hρ).trajectoryExpectedQ
        (qRobustMinusModel M ρ (2*ρ*M.effectiveHorizon) hρ).optimalGreedyPolicy -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖ + 2*ρ/(1-M.discount)^2) := by
  have hC : 0 ≤ 2*ρ/(1-M.discount)^2 := div_nonneg (mul_nonneg (by norm_num) hρ) (sq_nonneg _)
  constructor
  · apply qComparator_norm_le_of_pointwise _ _ _ hC
    intro s a
    exact (qComparator_source_distance_reduction M ρ hρ s a).1
  · apply qComparator_norm_le_of_pointwise _ _ _ hC
    intro s a
    exact (qComparator_source_distance_reduction M ρ hρ s a).2

end StatisticalRL.QLearning

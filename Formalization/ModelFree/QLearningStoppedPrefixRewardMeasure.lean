import Formalization.ModelFree.QLearningStoppedPrefixRewardMixture
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual stopped-prefix probability measure and bounded terminal-reward integral. -/
namespace StatisticalRL.QLearning.CountablePinsker
open MeasureTheory
open scoped ENNReal BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

local instance qRewardStoppedMeasurableSpace :
    MeasurableSpace (qStoppedPrefixAbsCarrier (State := State) (Action := Action)) := ⊤

/-- The genuine countable stopped law, using the existing actual prefix masses. -/
noncomputable def qRewardStopped_measure (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (γ : ℝ) (s : State) (a : Action) :
    Measure (qStoppedPrefixAbsCarrier (State := State) (Action := Action)) :=
  Measure.sum (fun z => ENNReal.ofReal (qActualStoppedPrefixMass M π γ s a z) •
    Measure.dirac z)

theorem qRewardStopped_measure_singleton (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (γ : ℝ) (s : State) (a : Action)
    (z : qStoppedPrefixAbsCarrier (State := State) (Action := Action)) :
    qRewardStopped_measure M π γ s a {z} =
      ENNReal.ofReal (qActualStoppedPrefixMass M π γ s a z) := by
  classical
  simp [qRewardStopped_measure, Measure.sum_apply, Measure.smul_apply,
    Set.indicator_apply, Set.mem_singleton_iff]

theorem qRewardStopped_measure_univ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (γ : ℝ) (s : State) (a : Action)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    qRewardStopped_measure M π γ s a Set.univ = 1 := by
  have hn : ∀ z : qStoppedPrefixAbsCarrier (State := State) (Action := Action),
      0 ≤ qActualStoppedPrefixMass M π γ s a z := by
    rintro ⟨k, path⟩
    exact mul_nonneg (qGeometricStopWeight_nonneg γ k hγ hγ1)
      ((qForcedPrefixLaw M π s a k).prob_nonneg path)
  have hs := qRewardStopped_mass_hasSum M π γ s a hγ hγ1
  simp only [qRewardStopped_measure, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hn hs.summable, hs.tsum_eq]
  norm_num

theorem qRewardStopped_payoff_measurable (M : DiscountedMDP State Action)
    (s : State) (a : Action) : Measurable (qRewardStopped_payoff M s a) :=
  measurable_of_countable _

theorem qRewardStopped_payoff_integrable (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (γ : ℝ) (s : State) (a : Action)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    Integrable (qRewardStopped_payoff M s a) (qRewardStopped_measure M π γ s a) := by
  letI : IsProbabilityMeasure (qRewardStopped_measure M π γ s a) :=
    ⟨qRewardStopped_measure_univ M π γ s a hγ hγ1⟩
  apply (integrable_const (1 : ℝ)).mono'
    (qRewardStopped_payoff_measurable M s a).aestronglyMeasurable
  filter_upwards [] with z
  rcases z with ⟨k, path⟩
  change ‖qPrefixTerminalReward M s a k path‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (qPrefixTerminalReward_bounds M s a k path).1]
  exact (qPrefixTerminalReward_bounds M s a k path).2

/-- The Bochner integral is identified with the already justified actual
mass-series mixture, not stipulated as a new expectation definition. -/
theorem qRewardStopped_integral_eq_mixture (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (γ : ℝ) (s : State) (a : Action)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    (∫ z, qRewardStopped_payoff M s a z ∂qRewardStopped_measure M π γ s a) =
      ∑' k, qGeometricStopWeight γ k * qPrefixRewardMean M π k s a := by
  rw [integral_countable' (qRewardStopped_payoff_integrable M π γ s a hγ hγ1)]
  have hreal (z : qStoppedPrefixAbsCarrier (State := State) (Action := Action)) :
      (qRewardStopped_measure M π γ s a).real {z} =
        qActualStoppedPrefixMass M π γ s a z := by
    rcases z with ⟨k, path⟩
    rw [measureReal_def, qRewardStopped_measure_singleton, ENNReal.toReal_ofReal]
    exact mul_nonneg (qGeometricStopWeight_nonneg γ k hγ hγ1)
      ((qForcedPrefixLaw M π s a k).prob_nonneg path)
  simp_rw [hreal, smul_eq_mul]
  exact qRewardStopped_payoff_mixture M π γ s a hγ hγ1

theorem qRewardStopped_integral_eq_trajectoryQ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    (∫ z, qRewardStopped_payoff M s a z
      ∂qRewardStopped_measure M π M.discount s a) =
      (1 - M.discount) * M.trajectoryExpectedQ π s a := by
  rw [qRewardStopped_integral_eq_mixture M π M.discount s a
    M.discount_nonneg M.discount_lt_one]
  simp_rw [qRewardStopped_weight_eq, mul_assoc]
  rw [tsum_mul_left, qPrefixRewardMean_tsum_eq_trajectoryQ]

end StatisticalRL.QLearning.CountablePinsker

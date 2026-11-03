import Formalization.ModelFree.QLearningStoppedPrefixKLAbsSummable
import Formalization.ModelFree.QLearningGeometricPrefixBellman

/-! Actual geometric stopped-law normalization and justified terminal-reward mixture. -/
namespace StatisticalRL.QLearning.CountablePinsker
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Zero-safe stop weights equal the usual geometric formula at every depth. -/
theorem qRewardStopped_weight_eq (γ : ℝ) (k : ℕ) :
    qGeometricStopWeight γ k = (1 - γ) * γ ^ k := by
  by_cases hz : γ = 0
  · subst γ
    cases k <;> simp [qGeometricStopWeight_zero]
  · simp [qGeometricStopWeight, hz]

theorem qRewardStopped_weights_hasSum (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    HasSum (qGeometricStopWeight γ) 1 := by
  have h := (hasSum_geometric_of_lt_one hγ hγ1).mul_left (1 - γ)
  simp_rw [← qRewardStopped_weight_eq] at h
  convert h using 1
  field_simp [ne_of_gt (sub_pos.mpr hγ1)]

/-- Normalization uses finite fiber sums and nonnegative sigma summability
before invoking real tsum regrouping. -/
theorem qRewardStopped_mass_hasSum (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (γ : ℝ) (s : State) (a : Action)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    HasSum (qActualStoppedPrefixMass M π γ s a) 1 := by
  have hn : ∀ z : qStoppedPrefixAbsCarrier (State := State) (Action := Action),
      0 ≤ qActualStoppedPrefixMass M π γ s a z := by
    rintro ⟨k, path⟩
    exact mul_nonneg (qGeometricStopWeight_nonneg γ k hγ hγ1)
      ((qForcedPrefixLaw M π s a k).prob_nonneg path)
  have hfiber (k : ℕ) :
      (∑' path : QForcedPrefix (State := State) (Action := Action) k,
        qActualStoppedPrefixMass M π γ s a ⟨k, path⟩) = qGeometricStopWeight γ k := by
    rw [tsum_fintype]
    change (∑ path, qGeometricStopWeight γ k * qForcedPrefixWeight M π s a k path) = _
    have hp : (∑ path, qForcedPrefixWeight M π s a k path) = 1 :=
      (qForcedPrefixLaw M π s a k).sum_prob
    rw [← Finset.mul_sum, hp, mul_one]
  have hs : Summable (qActualStoppedPrefixMass M π γ s a) := by
    apply (summable_sigma_of_nonneg hn).2
    constructor
    · intro k
      exact Summable.of_finite
    · simp_rw [hfiber]
      exact (qRewardStopped_weights_hasSum γ hγ hγ1).summable
  apply hs.hasSum_iff.mpr
  rw [hs.tsum_sigma]
  simp_rw [hfiber]
  exact (qRewardStopped_weights_hasSum γ hγ hγ1).tsum_eq

/-- Actual terminal reward on the depth-tagged stopped-prefix carrier. -/
def qRewardStopped_payoff (M : DiscountedMDP State Action) (s : State) (a : Action) :
    qStoppedPrefixAbsCarrier (State := State) (Action := Action) → ℝ
  | ⟨k, path⟩ => qPrefixTerminalReward M s a k path

/-- The payoff atom is dominated by the actual normalized probability mass.
This supplies summability rather than assuming the exchange-of-sums conclusion. -/
theorem qRewardStopped_payoff_summable (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (γ : ℝ) (s : State) (a : Action)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    Summable (fun z => qActualStoppedPrefixMass M π γ s a z *
      qRewardStopped_payoff M s a z) := by
  apply Summable.of_nonneg_of_le _ _
    (qRewardStopped_mass_hasSum M π γ s a hγ hγ1).summable
  · rintro ⟨k, path⟩
    exact mul_nonneg
      (mul_nonneg (qGeometricStopWeight_nonneg γ k hγ hγ1)
        ((qForcedPrefixLaw M π s a k).prob_nonneg path))
      (qPrefixTerminalReward_bounds M s a k path).1
  · rintro ⟨k, path⟩
    exact mul_le_of_le_one_right
      (mul_nonneg (qGeometricStopWeight_nonneg γ k hγ hγ1)
        ((qForcedPrefixLaw M π s a k).prob_nonneg path))
      (qPrefixTerminalReward_bounds M s a k path).2

/-- Regrouping is justified by the preceding derived summability theorem. -/
theorem qRewardStopped_payoff_mixture (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (γ : ℝ) (s : State) (a : Action)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    (∑' z, qActualStoppedPrefixMass M π γ s a z * qRewardStopped_payoff M s a z) =
      ∑' k, qGeometricStopWeight γ k * qPrefixRewardMean M π k s a := by
  rw [(qRewardStopped_payoff_summable M π γ s a hγ hγ1).tsum_sigma]
  apply tsum_congr
  intro k
  rw [tsum_fintype]
  change (∑ path, (qGeometricStopWeight γ k * qForcedPrefixWeight M π s a k path) *
    qPrefixTerminalReward M s a k path) = _
  unfold qPrefixRewardMean FiniteDistribution.expectation
  simp only [qForcedPrefixLaw]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro path _
  ring

/-- The actual stopped-mass reward series is the normalized actual trajectory Q.
The stop parameter is the model's discount, including discount zero. -/
theorem qRewardStopped_payoff_eq_trajectoryQ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (a : Action) :
    (∑' z, qActualStoppedPrefixMass M π M.discount s a z *
      qRewardStopped_payoff M s a z) =
      (1 - M.discount) * M.trajectoryExpectedQ π s a := by
  rw [qRewardStopped_payoff_mixture M π M.discount s a
    M.discount_nonneg M.discount_lt_one]
  simp_rw [qRewardStopped_weight_eq, mul_assoc]
  rw [tsum_mul_left, qPrefixRewardMean_tsum_eq_trajectoryQ]

end StatisticalRL.QLearning.CountablePinsker

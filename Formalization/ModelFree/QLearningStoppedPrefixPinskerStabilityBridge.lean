import Formalization.ModelFree.QLearningCountablePinskerProductionBridge
import Formalization.ModelFree.QLearningStoppedPrefixGeometricBound
import Formalization.ModelFree.QLearningStoppedPrefixStabilityAssembly
import Formalization.ModelFree.QLearningChiKL

/-! Actual supported stopped-law Pinsker and KL bounds imply transition-row stability. -/

open scoped BigOperators
namespace StatisticalRL.QLearning
open StatisticalRL.QLearning.CountablePinsker

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The KL quantity used by the Pinsker/geometric bridge, computed directly
from the actual stopped-prefix masses in selected-model/reference orientation.
This is the same atomic series used by the policy worker's measure adapter. -/
noncomputable def qCountableStoppedPrefixKL_forStability
    (M M' : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (γ : ℝ) (s : State) (a : Action) : ℝ :=
  ∑' z : qStoppedPrefixAbsCarrier (State := State) (Action := Action),
    klAtom (qActualStoppedPrefixMass M' π γ s a z)
      (qActualStoppedPrefixMass M π γ s a z)

/-- Compatibility with the geometric/policy adapter's distinct name for the
same zero-safe KL atom. This is a definitional bridge, not a measure-KL claim. -/
theorem qCountableStoppedPrefixKL_forStability_eq_stoppedAtom
    (M M' : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (γ : ℝ) (s : State) (a : Action) :
    qCountableStoppedPrefixKL_forStability M M' π γ s a =
      ∑' z : qStoppedPrefixAbsCarrier (State := State) (Action := Action),
        qStoppedPrefixKLAtom (qActualStoppedPrefixMass M' π γ s a z)
          (qActualStoppedPrefixMass M π γ s a z) := by
  simp [qCountableStoppedPrefixKL_forStability, klAtom,
    qStoppedPrefixKLAtom]

/-- Countable Pinsker gives the half-L1 distance of the two actual stopped
laws at most the square root of their actual oriented stopped KL divided by
two. Row support and row KL are the hypotheses used to establish the actual
prefix laws' support and absolute summability; no free KL parameter is assumed. -/
theorem qActualStoppedPrefixTV_le_sqrt_actualKL
    (M M' : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (ρ : ℝ) (s : State) (a : Action)
    (hρ : 0 ≤ ρ)
    (hrowSupport : ∀ x b y, (M'.transition x b).prob y ≠ 0 →
      (M.transition x b).prob y ≠ 0)
    (hrowKL : ∀ x b,
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun y ↦ (M'.transition x b).prob y)
        (fun y ↦ (M.transition x b).prob y) ≤ ρ) :
    qCountableTotalVariation
        (qActualStoppedPrefixMass M' π M.discount s a)
        (qActualStoppedPrefixMass M π M.discount s a) ≤
      Real.sqrt (qCountableStoppedPrefixKL_forStability
        M M' π M.discount s a / 2) := by
  let T := qCountableTotalVariation
    (qActualStoppedPrefixMass M' π M.discount s a)
    (qActualStoppedPrefixMass M π M.discount s a)
  let K := qCountableStoppedPrefixKL_forStability M M' π M.discount s a
  have hPinsker := qActualStoppedPrefixPinsker M M' π M.discount ρ s a
    M.discount_nonneg M.discount_lt_one hρ hrowSupport hrowKL
  have hT0K : 2 * T ^ 2 ≤ K := by
    dsimp [T, K, qCountableStoppedPrefixKL_forStability]
    simpa only [qCountableTotalVariation] using hPinsker
  have hT : 0 ≤ T := by
    dsimp [T, qCountableTotalVariation]
    exact mul_nonneg (by norm_num) (tsum_nonneg fun _ ↦ abs_nonneg _)
  have hK : 0 ≤ K := by nlinarith [sq_nonneg T]
  have hroot : 0 ≤ K / 2 := by positivity
  have hsq : T ^ 2 ≤ (Real.sqrt (K / 2)) ^ 2 := by
    rw [Real.sq_sqrt hroot]
    nlinarith [hT0K]
  exact (sq_le_sq₀ hT (Real.sqrt_nonneg _)).mp hsq

/-- Fixed-policy actual stopped-KL stability interface. The row assumptions
feed both countable Pinsker and the geometric KL estimate. Equal model rewards
make the actual terminal payoff common, while `qStopped_fixed_policy...`
performs the existing measure/reward transfer with these same stopped masses. -/
theorem qStopped_fixed_policy_stability_of_actual_rows
    (M M' : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (hr : M'.reward = M.reward) (hγ : M'.discount = M.discount)
    (ρ : ℝ) (s : State) (a : Action)
    (hρ : 0 ≤ ρ)
    (hrowSupport : ∀ x b y, (M'.transition x b).prob y ≠ 0 →
      (M.transition x b).prob y ≠ 0)
    (hrowKL : ∀ x b,
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun y ↦ (M'.transition x b).prob y)
        (fun y ↦ (M.transition x b).prob y) ≤ ρ) :
    |M'.trajectoryExpectedQ π s a - M.trajectoryExpectedQ π s a| ≤
      Real.sqrt (ρ * M.discount / (2 * (1 - M.discount) ^ 3)) := by
  let K := qCountableStoppedPrefixKL_forStability M M' π M.discount s a
  have hPinsker : (1 / 2 : ℝ) * ∑' z : qStoppedPrefixAbsCarrier
      (State := State) (Action := Action),
      |qActualStoppedPrefixMass M' π M.discount s a z -
        qActualStoppedPrefixMass M π M.discount s a z| ≤ Real.sqrt (K / 2) := by
    simpa [K, qCountableTotalVariation] using
      qActualStoppedPrefixTV_le_sqrt_actualKL M M' π ρ s a hρ hrowSupport hrowKL
  have hKL : K ≤ ρ * M.discount / (1 - M.discount) := by
    dsimp [K, qCountableStoppedPrefixKL_forStability]
    simpa [klAtom, qStoppedPrefixKLAtom] using
      qActualStoppedPrefixKL_le_geometric_bound M M' π M.discount ρ s a
        M.discount_nonneg M.discount_lt_one hρ hrowSupport hrowKL
  exact qStopped_fixed_policy_stability_of_pinsker_kl M M' π hr hγ ρ K s a
    hPinsker hKL

/-- The same actual row hypotheses provide the two common-policy inputs needed
for the source own-model optimal-greedy transfer. The two policies get their
own actual stopped laws; neither a uniform randomized-policy assumption nor a
target-shaped stability premise is introduced. -/
theorem qStopped_optimal_stability_of_actual_rows
    (M M' : DiscountedMDP State Action)
    (hr : M'.reward = M.reward) (hγ : M'.discount = M.discount)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hrowSupport : ∀ x b y, (M'.transition x b).prob y ≠ 0 →
      (M.transition x b).prob y ≠ 0)
    (hrowKL : ∀ x b,
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun y ↦ (M'.transition x b).prob y)
        (fun y ↦ (M.transition x b).prob y) ≤ ρ)
    (s : State) (a : Action) :
    |M'.trajectoryExpectedQ M'.optimalGreedyPolicy s a -
      M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
      Real.sqrt (ρ * M.discount / (2 * (1 - M.discount) ^ 3)) := by
  apply qStopped_optimal_transfer_of_two_policy_bounds M M'
  · intro x b
    exact qStopped_fixed_policy_stability_of_actual_rows M M'
      M'.optimalGreedyPolicy hr hγ ρ x b hρ hrowSupport hrowKL
  · intro x b
    exact qStopped_fixed_policy_stability_of_actual_rows M M'
      M.optimalGreedyPolicy hr hγ ρ x b hρ hrowSupport hrowKL

/-- Robust transition-row χ² balls discharge the exact support and KL
premises of the actual stopped-law interface through the production finite
row KL theorem. The resulting stability estimate still uses the actual
stopped masses and common model reward. -/
theorem qStopped_optimal_stability_of_chiBall_rows
    (M M' : DiscountedMDP State Action)
    (hr : M'.reward = M.reward) (hγ : M'.discount = M.discount)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hballs : ∀ x b, M'.transition x b ∈ qChiBall (M.transition x b) ρ)
    (s : State) (a : Action) :
    |M'.trajectoryExpectedQ M'.optimalGreedyPolicy s a -
      M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
      Real.sqrt (ρ * M.discount / (2 * (1 - M.discount) ^ 3)) := by
  have hrowSupport : ∀ x b y, (M'.transition x b).prob y ≠ 0 →
      (M.transition x b).prob y ≠ 0 := by
    intro x b y hcandidate
    by_contra hnominal
    exact hcandidate ((hballs x b).1 y hnominal)
  have hrowKL : ∀ x b,
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun y ↦ (M'.transition x b).prob y)
        (fun y ↦ (M.transition x b).prob y) ≤ ρ := by
    intro x b
    exact (qChi_finiteKLExpression_le (M.transition x b)
      (M'.transition x b) (hballs x b).1).trans (hballs x b).2
  exact qStopped_optimal_stability_of_actual_rows M M' hr hγ ρ hρ
    hrowSupport hrowKL s a

end StatisticalRL.QLearning

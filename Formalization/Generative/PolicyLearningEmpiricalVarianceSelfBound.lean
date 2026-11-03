import Formalization.Generative.ModelBasedPolicyLearning
import Formalization.Generative.PolicyEvaluationVariance

/-! Exact empirical-value variance expansion and bounded self-normalization
arithmetic. The true-resolvent order/Jensen bridge is not assumed or asserted. -/
namespace StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Empirical-minus-true transition error applied to the empirical actual value. -/
noncomputable def empiricalPolicyValueResidual (M H : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : ℝ :=
  (H.policyTransition π s).expectation (H.trajectoryExpectedValue π) -
    (M.policyTransition π s).expectation (H.trajectoryExpectedValue π)

/-- The empirical actual value obeys its same-known-reward Bellman equation. -/
theorem empiricalPolicyValue_bellman (M H : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (hr : H.reward = M.reward)
    (hγ : H.discount = M.discount) (s : State) :
    H.trajectoryExpectedValue π s = evaluationPolicyReward M π s +
      M.discount * (H.policyTransition π s).expectation (H.trajectoryExpectedValue π) := by
  have hb := evaluationTrajectory_bellman H π s
  change H.trajectoryExpectedValue π s = (π s).expectation (H.reward s) +
    H.discount * (H.policyTransition π s).expectation (H.trajectoryExpectedValue π) at hb
  rw [hr, hγ] at hb
  exact hb

/-- Exact source second-moment identity with all residual signs and γ powers. -/
theorem empiricalPolicyValue_variance_identity (M H : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (hr : H.reward = M.reward)
    (hγ : H.discount = M.discount) (s : State) :
    M.discount ^ 2 * (M.policyTransition π s).variance (H.trajectoryExpectedValue π) =
      M.discount ^ 2 * (M.policyTransition π s).expectation
        (fun t ↦ (H.trajectoryExpectedValue π t) ^ 2) -
      (H.trajectoryExpectedValue π s) ^ 2 +
      2 * H.trajectoryExpectedValue π s * evaluationPolicyReward M π s -
      (evaluationPolicyReward M π s) ^ 2 +
      2 * M.discount * (H.trajectoryExpectedValue π s - evaluationPolicyReward M π s) *
        empiricalPolicyValueResidual M H π s -
      M.discount ^ 2 * (empiricalPolicyValueResidual M H π s) ^ 2 := by
  have hb := empiricalPolicyValue_bellman M H π hr hγ s
  have heq : M.discount * (M.policyTransition π s).expectation (H.trajectoryExpectedValue π) =
      H.trajectoryExpectedValue π s - evaluationPolicyReward M π s -
        M.discount * empiricalPolicyValueResidual M H π s := by
    unfold empiricalPolicyValueResidual
    linarith only [hb]
  have hsq := congrArg (fun t : ℝ ↦ t ^ 2) heq
  unfold FiniteDistribution.variance
  nlinarith only [hsq]

/-- Actual empirical continuation reward has the source interval bounds. -/
theorem empiricalPolicyValue_continuation_bounds (M H : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (hr : H.reward = M.reward)
    (hγ : H.discount = M.discount) (s : State) :
    0 ≤ H.trajectoryExpectedValue π s - evaluationPolicyReward M π s ∧
      H.trajectoryExpectedValue π s - evaluationPolicyReward M π s ≤
        M.discount / (1 - M.discount) := by
  have hb := empiricalPolicyValue_bellman M H π hr hγ s
  have hnon : 0 ≤ (H.policyTransition π s).expectation (H.trajectoryExpectedValue π) :=
    (H.policyTransition π s).expectation_nonneg (fun t ↦ (H.trajectoryExpectedValue_bounds π t).1)
  have hup : (H.policyTransition π s).expectation (H.trajectoryExpectedValue π) ≤
      1 / (1 - M.discount) := by
    apply (H.policyTransition π s).expectation_le_const
    intro t
    simpa only [hγ] using (H.trajectoryExpectedValue_bounds π t).2
  have hp := mul_nonneg M.discount_nonneg hnon
  have hmul := mul_le_mul_of_nonneg_left hup M.discount_nonneg
  simp only [div_eq_mul_inv, one_mul] at hmul ⊢
  constructor <;> nlinarith only [hb, hp, hmul]

/-- Source pointwise self-bounding variance inequality, valid at γ=0.
All value/reward/continuation bounds are derived from actual MDP semantics. -/
theorem empiricalPolicyValue_variance_selfBound (M H : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (hr : H.reward = M.reward)
    (hγ : H.discount = M.discount) (s : State) :
    M.discount ^ 2 * (M.policyTransition π s).variance (H.trajectoryExpectedValue π) ≤
      M.discount * (M.policyTransition π s).expectation
        (fun t ↦ (H.trajectoryExpectedValue π t) ^ 2) -
      (H.trajectoryExpectedValue π s) ^ 2 + 2 / (1 - M.discount) +
      (2 * M.discount ^ 2 / (1 - M.discount)) * |empiricalPolicyValueResidual M H π s| := by
  let W := H.trajectoryExpectedValue π
  let r := evaluationPolicyReward M π s
  let z := empiricalPolicyValueResidual M H π s
  have hid := empiricalPolicyValue_variance_identity M H π hr hγ s
  change M.discount ^ 2 * (M.policyTransition π s).variance W =
    M.discount ^ 2 * (M.policyTransition π s).expectation (fun t ↦ W t ^ 2) - W s ^ 2 +
      2 * W s * r - r ^ 2 + 2 * M.discount * (W s - r) * z - M.discount ^ 2 * z ^ 2 at hid
  have hW := H.trajectoryExpectedValue_bounds π s
  rw [hγ] at hW
  change 0 ≤ W s ∧ W s ≤ 1 / (1 - M.discount) at hW
  have hr1 : r ≤ 1 := (π s).expectation_le_const (M.reward_le_one s)
  have hWr : W s * r ≤ 1 / (1 - M.discount) :=
    (mul_le_mul_of_nonneg_left hr1 hW.1).trans (by simpa using hW.2)
  have hcont := empiricalPolicyValue_continuation_bounds M H π hr hγ s
  change 0 ≤ W s - r ∧ W s - r ≤ M.discount / (1 - M.discount) at hcont
  have hγsq : M.discount ^ 2 ≤ M.discount := by nlinarith [M.discount_nonneg, M.discount_lt_one]
  have hE : 0 ≤ (M.policyTransition π s).expectation (fun t ↦ W t ^ 2) :=
    (M.policyTransition π s).expectation_nonneg (fun _ ↦ sq_nonneg _)
  have hEmul := mul_le_mul_of_nonneg_right hγsq hE
  have hcross₁ := mul_le_mul_of_nonneg_left (le_abs_self z)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) M.discount_nonneg) hcont.1)
  have hcross₂ := mul_le_mul_of_nonneg_right hcont.2
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) M.discount_nonneg) (abs_nonneg z))
  have hcross : 2 * M.discount * (W s - r) * z ≤
      (2 * M.discount ^ 2 / (1 - M.discount)) * |z| := by
    simp only [div_eq_mul_inv] at hcross₁ hcross₂ ⊢
    nlinarith only [hcross₁, hcross₂]
  have hsq : 0 ≤ M.discount ^ 2 * z ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  change M.discount ^ 2 * (M.policyTransition π s).variance W ≤ _
  dsimp [z, W] at hid hWr hEmul hcross hsq ⊢
  simp only [div_eq_mul_inv, one_mul] at hid hWr hEmul hcross hsq ⊢
  nlinarith only [hid, hWr, hEmul, hcross, hsq, sq_nonneg r]

end StatisticalRL.DiscountedMDP

namespace StatisticalRL.ModelBasedPolicyLearning
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Source pointwise variance expansion applies to the actual fitted empirical
optimal value and its data-dependent deterministic greedy policy. -/
theorem policyEstimator_empiricalVariance_selfBound (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) (s : State) :
    let π := fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)
    M.discount ^ 2 * (M.policyTransition π s).variance (valueEstimator M N hN data) ≤
      M.discount * (M.policyTransition π s).expectation (fun t ↦ (valueEstimator M N hN data t) ^ 2) -
      (valueEstimator M N hN data s) ^ 2 + 2 / (1 - M.discount) +
      (2 * M.discount ^ 2 / (1 - M.discount)) *
        |empiricalPolicyValueResidual M (empiricalModel M N hN data) π s| := by
  exact empiricalPolicyValue_variance_selfBound M (empiricalModel M N hN data)
    (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) rfl rfl s

/-- The AM-GM step used to solve the source's scalar self-bounding inequality. -/
theorem policyLearning_selfBound_amgm (B S : ℝ) (hB : 0 ≤ B) (hS : 0 ≤ S) :
    Real.sqrt (2 * B * S) ≤ B + S / 2 := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_nonneg (B - S / 2)]

/-- Solve the exact source scalar relation. It is a conditional numerical
lemma, not a replacement for proving the empirical true-resolvent bridge. -/
theorem policyLearning_selfBound_solve (A B S : ℝ) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hself : S ≤ A + 2 * B + Real.sqrt (2 * B * S)) :
    S ≤ 2 * A + 6 * B := by
  have h := policyLearning_selfBound_amgm B S hB hS
  linarith

end StatisticalRL.ModelBasedPolicyLearning

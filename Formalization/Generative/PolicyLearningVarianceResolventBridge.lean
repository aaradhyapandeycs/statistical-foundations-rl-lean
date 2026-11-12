import Formalization.Generative.PolicyLearningTrueResolventJensen
import Formalization.Generative.PolicyLearningEmpiricalVarianceSelfBound

/-!
# Empirical-value variance through the true-policy resolvent

This is a deterministic bridge. It makes no independence claim and does not
assume the true-kernel forcing of the empirical value is nonnegative.
-/

open scoped Matrix

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance varianceBridgeStateDecidable : DecidableEq State := Classical.decEq State

/-- Apply the true resolvent to the actual empirical-value variance self-bound.
The empirical and true models share known reward and discount, while their
transition kernels may be arbitrary. -/
theorem empiricalPolicyValue_variance_resolvent_bound (M H : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (hr : H.reward = M.reward)
    (hγ : H.discount = M.discount) :
    M.discount ^ 2 * ‖truePolicyResolvent M π *ᵥ
      (fun s ↦ (M.policyTransition π s).variance (H.trajectoryExpectedValue π))‖ ≤
      2 / (1 - M.discount) ^ 2 + (2 * M.discount ^ 2 / (1 - M.discount)) *
        ‖truePolicyResolvent M π *ᵥ (fun s ↦ |empiricalPolicyValueResidual M H π s|)‖ := by
  let h := 1 - M.discount
  let A : Matrix State State ℝ := 1 - M.discount • evaluationPolicyMatrix M π
  let R := truePolicyResolvent M π
  let W := H.trajectoryExpectedValue π
  let W2 : State → ℝ := fun s ↦ W s ^ 2
  let σ : State → ℝ := fun s ↦ (M.policyTransition π s).variance W
  let z : State → ℝ := fun s ↦ |empiricalPolicyValueResidual M H π s|
  let one : State → ℝ := fun _ ↦ 1
  let c : ℝ := 2 * M.discount ^ 2 / h
  let k : ℝ := 2 / h
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hσ (s : State) : 0 ≤ σ s := (M.policyTransition π s).variance_nonneg W
  have hpoint (s : State) : (M.discount ^ 2 • σ) s ≤
      (-(A *ᵥ W2) + k • one + c • z) s := by
    have hs := empiricalPolicyValue_variance_selfBound M H π hr hγ s
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] 
    change M.discount ^ 2 * (M.policyTransition π s).variance W ≤ _
    dsimp [A, W2, σ, z, one, c, k, h]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evaluationPolicyMatrix_mulVec]
    linarith
  have hRone : R *ᵥ one = fun _ ↦ 1 / h := truePolicyResolvent_mulVec_one M π
  have hRA : R *ᵥ (A *ᵥ W2) = W2 := by
    letI : Invertible A := (evaluationPolicyResolvent_isUnit M π).invertible
    change A⁻¹ *ᵥ (A *ᵥ W2) = W2
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hRσ (s : State) : 0 ≤ (R *ᵥ σ) s := truePolicyResolvent_mulVec_nonneg M π σ hσ s
  have hRz (s : State) : 0 ≤ (R *ᵥ z) s :=
    truePolicyResolvent_mulVec_nonneg M π z (fun _ ↦ abs_nonneg _) s
  have hs (s : State) : M.discount ^ 2 * (R *ᵥ σ) s ≤
      k / h + c * ‖R *ᵥ z‖ := by
    have hm := truePolicyResolvent_mulVec_mono M π (M.discount ^ 2 • σ)
      (-(A *ᵥ W2) + k • one + c • z) hpoint s
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_neg,
      Matrix.mulVec_smul, Matrix.mulVec_smul, hRA, hRone] at hm
    simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul] at hm
    have hv : (R *ᵥ z) s ≤ ‖R *ᵥ z‖ := (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (R *ᵥ z) s))
    have hmul := mul_le_mul_of_nonneg_left hv hc
    simp only [div_eq_mul_inv, one_mul] at hm ⊢
    nlinarith [sq_nonneg (W s)]
  have hbound : ‖M.discount ^ 2 • (R *ᵥ σ)‖ ≤ k / h + c * ‖R *ᵥ z‖ := by
    apply (pi_norm_le_iff_of_nonneg (add_nonneg (div_nonneg hk hh.le)
      (mul_nonneg hc (norm_nonneg _)))).2
    intro s
    simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (hRσ s))]
    exact hs s
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hbound
  convert hbound using 1
  dsimp [k, c, h, R, σ, W, z]
  field_simp

/-- Conditional deterministic self-bounding inequality obtained from a
pointwise residual input and the derived empirical variance expansion. It
holds for every realized policy and does not assume nonnegative forcing. -/
theorem empiricalPolicyValue_selfBounding_residual
    (M H : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (hr : H.reward = M.reward) (hγ : H.discount = M.discount)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrow : ∀ s, |empiricalPolicyValueResidual M H π s| ≤
      a * Real.sqrt ((M.policyTransition π s).variance (H.trajectoryExpectedValue π)) + b) :
    let S := M.discount * ‖truePolicyResolvent M π *ᵥ
      (fun s ↦ |empiricalPolicyValueResidual M H π s|)‖
    S ≤ a * Real.sqrt (2 / (1 - M.discount) ^ 3 +
      2 * M.discount / (1 - M.discount) ^ 2 * S) +
        M.discount * b / (1 - M.discount) := by
  let h := 1 - M.discount
  let R := truePolicyResolvent M π
  let σ : State → ℝ := fun s ↦ (M.policyTransition π s).variance (H.trajectoryExpectedValue π)
  let z := empiricalPolicyValueResidual M H π
  let Z := R *ᵥ (fun s ↦ |z s|)
  let V := R *ᵥ σ
  let S := M.discount * ‖Z‖
  let X := ‖V‖ / h
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hS : 0 ≤ S := mul_nonneg M.discount_nonneg (norm_nonneg _)
  have hX : 0 ≤ X := div_nonneg (norm_nonneg _) hh.le
  have hσ (s : State) : 0 ≤ σ s := (M.policyTransition π s).variance_nonneg _
  have hv := empiricalPolicyValue_variance_resolvent_bound M H π hr hγ
  change M.discount ^ 2 * ‖V‖ ≤ 2 / h ^ 2 + (2 * M.discount ^ 2 / h) * ‖Z‖ at hv
  have hdivide := div_le_div_of_nonneg_right hv hh.le
  have hXbound : M.discount ^ 2 * X ≤ 2 / h ^ 3 + 2 * M.discount / h ^ 2 * S := by
    dsimp [X, S]
    calc
      _ = (M.discount ^ 2 * ‖V‖) / h := by ring
      _ ≤ (2 / h ^ 2 + (2 * M.discount ^ 2 / h) * ‖Z‖) / h := hdivide
      _ = _ := by field_simp
  have hroot : M.discount * Real.sqrt X ≤
      Real.sqrt (2 / h ^ 3 + 2 * M.discount / h ^ 2 * S) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt hX]
    exact hXbound
  have hrw := truePolicyResolvent_abs_residual_bound M π z σ a b hσ ha hb hrow
  change S ≤ M.discount * a * Real.sqrt X + M.discount * b / h at hrw
  have hm := mul_le_mul_of_nonneg_left hroot ha
  change S ≤ a * Real.sqrt (2 / h ^ 3 + 2 * M.discount / h ^ 2 * S) +
    M.discount * b / h
  nlinarith only [hrw, hm]

/-- The source's deterministic residual estimate at the exact β constants.
The only statistical input is the explicitly stated pointwise row inequality. -/
theorem empiricalPolicyValue_source_residual_bound
    (M H : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (hr : H.reward = M.reward) (hγ : H.discount = M.discount)
    (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 ≤ β)
    (hrow : ∀ s, |empiricalPolicyValueResidual M H π s| ≤
      Real.sqrt (β / N) * Real.sqrt ((M.policyTransition π s).variance (H.trajectoryExpectedValue π)) +
        2 * β / (N * (1 - M.discount))) :
    M.discount * ‖truePolicyResolvent M π *ᵥ
      (fun s ↦ |empiricalPolicyValueResidual M H π s|)‖ ≤
      2 * Real.sqrt (2 * β / (N * (1 - M.discount) ^ 3)) +
        6 * β / (N * (1 - M.discount) ^ 2) := by
  let h := 1 - M.discount
  let S := M.discount * ‖truePolicyResolvent M π *ᵥ
    (fun s ↦ |empiricalPolicyValueResidual M H π s|)‖
  let B := β / (N * h ^ 2)
  let A := Real.sqrt (2 * β / (N * h ^ 3))
  let a := Real.sqrt (β / N)
  let C := 2 / h ^ 3 + 2 * M.discount / h ^ 2 * S
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : 0 ≤ S := mul_nonneg M.discount_nonneg (norm_nonneg _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hC : 0 ≤ C := by
    have hg := M.discount_nonneg
    dsimp [C]
    positivity
  have ha2 : a ^ 2 = β / N := Real.sq_sqrt (div_nonneg hβ hn.le)
  have hA2 : A ^ 2 = 2 * β / (N * h ^ 3) := by dsimp [A]; rw [Real.sq_sqrt]; positivity
  have hsqrt2BS : (Real.sqrt (2 * B * S)) ^ 2 = 2 * B * S :=
    Real.sq_sqrt (by positivity)
  have hratio : (β / N) * C ≤ A ^ 2 + 2 * B * S := by
    rw [hA2]
    dsimp [B, C]
    have hgap : 0 ≤ β * S * (1 - M.discount) :=
      mul_nonneg (mul_nonneg hβ hS) (sub_nonneg.mpr M.discount_lt_one.le)
    have hgap2 := mul_nonneg hgap hh.le
    field_simp
    nlinarith only [hgap2]
  have hsq : (a * Real.sqrt C) ^ 2 ≤ (A + Real.sqrt (2 * B * S)) ^ 2 := by
    rw [mul_pow, ha2, Real.sq_sqrt hC, add_sq, hsqrt2BS]
    have hcross := mul_nonneg hA (Real.sqrt_nonneg (2 * B * S))
    nlinarith only [hratio, hcross]
  have hsqr := (sq_le_sq₀ (mul_nonneg ha (Real.sqrt_nonneg _))
    (add_nonneg hA (Real.sqrt_nonneg _))).mp hsq
  have hb : 0 ≤ 2 * β / (N * h) := by positivity
  have hself := empiricalPolicyValue_selfBounding_residual M H π hr hγ a (2 * β / (N * h))
    ha hb hrow
  change S ≤ a * Real.sqrt C + M.discount * (2 * β / (N * h)) / h at hself
  have hlinear : M.discount * (2 * β / (N * h)) / h ≤ 2 * B := by
    dsimp [B]
    have hmul := mul_le_mul_of_nonneg_right M.discount_lt_one.le (show 0 ≤ 2 * β by positivity)
    field_simp
    nlinarith only [hmul]
  have hrelation : S ≤ A + 2 * B + Real.sqrt (2 * B * S) := by linarith
  have hfinal := ModelBasedPolicyLearning.policyLearning_selfBound_solve A B S hB hS hrelation
  change S ≤ _
  dsimp [A, B, h] at hfinal
  convert hfinal using 1
  ring

/-- The true-policy resolvent maps entrywise absolute value to an upper
bound on the absolute inverse image. -/
theorem truePolicyResolvent_abs_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f : State → ℝ) (s : State) :
    |(truePolicyResolvent M π *ᵥ f) s| ≤
      (truePolicyResolvent M π *ᵥ (fun t ↦ |f t|)) s := by
  have hup := truePolicyResolvent_mulVec_mono M π f (fun t ↦ |f t|) (fun _ ↦ le_abs_self _) s
  have hlo := truePolicyResolvent_mulVec_mono M π (-f) (fun t ↦ |f t|) (fun _ ↦ neg_le_abs _) s
  rw [Matrix.mulVec_neg] at hlo
  simp only [Pi.neg_apply] at hlo
  exact abs_le.mpr ⟨by linarith, hup⟩

/-- Exact source identity with the true inverse acting on the empirical-value
residual, for any two valid same-reward and same-discount models. -/
theorem empiricalPolicyValue_true_resolvent_identity (M H : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (hr : H.reward = M.reward)
    (hγ : H.discount = M.discount) :
    H.trajectoryExpectedValue π - M.trajectoryExpectedValue π =
      M.discount • (truePolicyResolvent M π *ᵥ empiricalPolicyValueResidual M H π) := by
  let A : Matrix State State ℝ := 1 - M.discount • evaluationPolicyMatrix M π
  letI : Invertible A := (evaluationPolicyResolvent_isUnit M π).invertible
  let W := H.trajectoryExpectedValue π
  let V := M.trajectoryExpectedValue π
  let z := empiricalPolicyValueResidual M H π
  have heq : A *ᵥ (W - V) = M.discount • z := by
    funext s
    have hw := empiricalPolicyValue_bellman M H π hr hγ s
    have hv := evaluationTrajectory_bellman M π s
    change W s = evaluationPolicyReward M π s + M.discount *
      (H.policyTransition π s).expectation W at hw
    change V s = evaluationPolicyReward M π s + M.discount *
      (M.policyTransition π s).expectation V at hv
    have hd := (M.policyTransition π s).expectation_sub W V
    simp only [A, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evaluationPolicyMatrix_mulVec]
    change W s - V s - M.discount *
      (M.policyTransition π s).expectation (W - V) = M.discount * z s
    change (M.policyTransition π s).expectation (W - V) = _ at hd
    change W s - V s - M.discount * (M.policyTransition π s).expectation (W - V) =
      M.discount * ((H.policyTransition π s).expectation W - (M.policyTransition π s).expectation W)
    rw [hd]
    nlinarith only [hw, hv]
  have hi := Matrix.inv_mulVec_eq_vec heq.symm
  change truePolicyResolvent M π *ᵥ (M.discount • z) = W - V at hi
  rw [Matrix.mulVec_smul] at hi
  exact hi.symm

/-- The true-resolvent absolute residual controls the actual fitted-policy
value-evaluation error, with no assumption on the forcing's sign. -/
theorem empiricalPolicyValue_error_le_resolvent_residual (M H : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (hr : H.reward = M.reward)
    (hγ : H.discount = M.discount) :
    ‖H.trajectoryExpectedValue π - M.trajectoryExpectedValue π‖ ≤
      M.discount * ‖truePolicyResolvent M π *ᵥ
        (fun s ↦ |empiricalPolicyValueResidual M H π s|)‖ := by
  let R := truePolicyResolvent M π
  let z := empiricalPolicyValueResidual M H π
  have hn : ‖R *ᵥ z‖ ≤ ‖R *ᵥ (fun s ↦ |z s|)‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro s
    rw [Real.norm_eq_abs]
    exact (truePolicyResolvent_abs_le M π z s).trans
      ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (R *ᵥ (fun s ↦ |z s|)) s)))
  rw [empiricalPolicyValue_true_resolvent_identity M H π hr hγ,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg M.discount_nonneg]
  exact mul_le_mul_of_nonneg_left hn M.discount_nonneg

/-- The source's fitted-policy evaluation-error bound follows deterministically
from the explicitly stated statewise residual inequality. -/
theorem empiricalPolicyValue_source_error_bound
    (M H : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (hr : H.reward = M.reward) (hγ : H.discount = M.discount)
    (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 ≤ β)
    (hrow : ∀ s, |empiricalPolicyValueResidual M H π s| ≤
      Real.sqrt (β / N) * Real.sqrt ((M.policyTransition π s).variance (H.trajectoryExpectedValue π)) +
        2 * β / (N * (1 - M.discount))) :
    ‖H.trajectoryExpectedValue π - M.trajectoryExpectedValue π‖ ≤
      2 * Real.sqrt (2 * β / (N * (1 - M.discount) ^ 3)) +
        6 * β / (N * (1 - M.discount) ^ 2) :=
  (empiricalPolicyValue_error_le_resolvent_residual M H π hr hγ).trans
    (empiricalPolicyValue_source_residual_bound M H π hr hγ N hN β hβ hrow)

end StatisticalRL.DiscountedMDP

namespace StatisticalRL.ModelBasedPolicyLearning
open StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Conditional fitted-policy specialization for the actual empirical MDP and
its actual data-dependent greedy policy. The statewise residual input must be
supplied by a separate simultaneous event. -/
theorem policyEstimator_source_error_bound_conditional (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State Action N) (β : ℝ) (hβ : 0 ≤ β)
    (hrow : ∀ s,
      |empiricalPolicyValueResidual M (empiricalModel M N hN data)
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s| ≤
      Real.sqrt (β / N) * Real.sqrt ((M.policyTransition
        (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) s).variance
          (valueEstimator M N hN data)) + 2 * β / (N * (1 - M.discount))) :
    ‖valueEstimator M N hN data - M.trajectoryExpectedValue
      (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t))‖ ≤
      2 * Real.sqrt (2 * β / (N * (1 - M.discount) ^ 3)) +
        6 * β / (N * (1 - M.discount) ^ 2) := by
  exact empiricalPolicyValue_source_error_bound M (empiricalModel M N hN data)
    (fun t ↦ EnvironmentStage.pointMass (policyEstimator M N hN data t)) rfl rfl N hN β hβ hrow

end StatisticalRL.ModelBasedPolicyLearning

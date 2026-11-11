import Formalization.Generative.PolicyEvaluationVarianceResolvent

/-! True-policy variance resolvent for arbitrary nonnegative forcing.
Normalize the forcing into a genuine bounded-reward MDP with the same kernel,
then transfer the actual-trajectory variance bound by exact scalar identities. -/

open scoped Matrix
namespace StatisticalRL.DiscountedMDP
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance : DecidableEq State := Classical.decEq State

/-- Literal true-policy inverse applied to arbitrary fixed forcing. -/
noncomputable def forcingPolicyValue (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f : State → ℝ) : State → ℝ :=
  (1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ f

/-- A positive normalizing scale, valid also for the zero forcing. -/
noncomputable def forcingScale (f : State → ℝ) : ℝ := max 1 ‖f‖

theorem forcingScale_pos (f : State → ℝ) : 0 < forcingScale f :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- A genuine same-kernel model with the normalized state reward. -/
noncomputable def normalizedForcingModel (M : DiscountedMDP State Action)
    (f : State → ℝ) (hf : ∀ s, 0 ≤ f s) : DiscountedMDP State Action where
  state_nonempty := M.state_nonempty
  action_nonempty := M.action_nonempty
  transition := M.transition
  reward := fun s _ ↦ f s / forcingScale f
  reward_nonneg := fun s _ ↦ div_nonneg (hf s) (forcingScale_pos f).le
  reward_le_one := by
    intro s a
    apply (div_le_one (forcingScale_pos f)).2
    have hn : |f s| ≤ ‖f‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm f s
    exact (le_abs_self _).trans (hn.trans (le_max_right _ _))
  discount := M.discount
  discount_nonneg := M.discount_nonneg
  discount_lt_one := M.discount_lt_one

/-- Normalized rewards have their actual trajectory value given by the same inverse. -/
theorem normalizedForcingModel_value (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f : State → ℝ) (hf : ∀ s, 0 ≤ f s) :
    forcingPolicyValue M π (fun s ↦ f s / forcingScale f) =
      (normalizedForcingModel M f hf).trajectoryExpectedValue π := by
  let H := normalizedForcingModel M f hf
  let A : Matrix State State ℝ := 1 - M.discount • evaluationPolicyMatrix M π
  letI : Invertible A := (evaluationPolicyResolvent_isUnit M π).invertible
  apply Matrix.inv_mulVec_eq_vec
  funext s
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evaluationPolicyMatrix_mulVec]
  have hb := evaluationTrajectory_bellman H π s
  change H.trajectoryExpectedValue π s =
    (π s).expectation (fun _ ↦ f s / forcingScale f) +
      M.discount * (M.policyTransition π s).expectation (H.trajectoryExpectedValue π) at hb
  rw [FiniteDistribution.expectation_const] at hb
  linarith

/-- The arbitrary-forcing value is a positive scalar times an actual trajectory value. -/
theorem forcingPolicyValue_eq_scaled_trajectory (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f : State → ℝ) (hf : ∀ s, 0 ≤ f s) :
    forcingPolicyValue M π f = forcingScale f •
      (normalizedForcingModel M f hf).trajectoryExpectedValue π := by
  rw [← normalizedForcingModel_value M π f hf]
  unfold forcingPolicyValue
  rw [← Matrix.mulVec_smul]
  congr 1
  funext s
  simp only [Pi.smul_apply, smul_eq_mul]
  exact (mul_div_cancel₀ (f s) (ne_of_gt (forcingScale_pos f))).symm

theorem forcingPolicyValue_nonneg (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f : State → ℝ) (hf : ∀ s, 0 ≤ f s) (s : State) :
    0 ≤ forcingPolicyValue M π f s := by
  rw [forcingPolicyValue_eq_scaled_trajectory M π f hf]
  exact mul_nonneg (forcingScale_pos f).le
    ((normalizedForcingModel M f hf).trajectoryExpectedValue_bounds π s).1

/-- Exact variance scaling for the project's finite probability rows. -/
theorem forcing_variance_const_mul (d : FiniteDistribution State) (c : ℝ) (V : State → ℝ) :
    d.variance (fun s ↦ c * V s) = c ^ 2 * d.variance V := by
  unfold FiniteDistribution.variance
  simp_rw [mul_pow]
  rw [FiniteDistribution.expectation_mul, FiniteDistribution.expectation_mul]
  ring

/-- Exact standard-deviation scaling for a nonnegative scalar. -/
theorem forcing_sqrt_variance_const_mul (d : FiniteDistribution State)
    (c : ℝ) (hc : 0 ≤ c) (V : State → ℝ) :
    Real.sqrt (d.variance (fun s ↦ c * V s)) = c * Real.sqrt (d.variance V) := by
  rw [forcing_variance_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- General source auxiliary-level bound, with no upper bound on the forcing.
The value inside the variance is the literal true-policy inverse applied to f. -/
theorem forcingPolicyValue_varianceResolvent_bound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f : State → ℝ) (hf : ∀ s, 0 ≤ f s) :
    M.discount * ‖(1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      (fun s ↦ Real.sqrt ((M.policyTransition π s).variance (forcingPolicyValue M π f)))‖ ≤
      ‖forcingPolicyValue M π f‖ / Real.sqrt (1 - M.discount) := by
  let H := normalizedForcingModel M f hf
  let C := forcingScale f
  let V := H.trajectoryExpectedValue π
  have hC : 0 < C := forcingScale_pos f
  have hV : forcingPolicyValue M π f = C • V := forcingPolicyValue_eq_scaled_trajectory M π f hf
  have hvec : (fun s ↦ Real.sqrt ((M.policyTransition π s).variance (forcingPolicyValue M π f))) =
      C • (fun s ↦ Real.sqrt (H.evaluationPolicyVariance π s)) := by
    funext s
    rw [hV]
    change Real.sqrt ((M.policyTransition π s).variance (fun t ↦ C * V t)) =
      C * Real.sqrt ((M.policyTransition π s).variance V)
    exact forcing_sqrt_variance_const_mul _ C hC.le V
  have hb := H.evaluationPolicyResolvent_sqrtVariance_bound π
  change M.discount * ‖(1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
    (fun s ↦ Real.sqrt (H.evaluationPolicyVariance π s))‖ ≤
      ‖V‖ / Real.sqrt (1 - M.discount) at hb
  rw [hvec, Matrix.mulVec_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hC,
    hV, norm_smul, Real.norm_eq_abs, abs_of_pos hC]
  have hm := mul_le_mul_of_nonneg_left hb hC.le
  convert hm using 1 <;> ring

/-- The literal inverse value solves the source's auxiliary Bellman equation. -/
theorem forcingPolicyValue_bellman (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f : State → ℝ) (s : State) :
    forcingPolicyValue M π f s = f s + M.discount *
      (M.policyTransition π s).expectation (forcingPolicyValue M π f) := by
  let A : Matrix State State ℝ := 1 - M.discount • evaluationPolicyMatrix M π
  letI : Invertible A := (evaluationPolicyResolvent_isUnit M π).invertible
  have he : A *ᵥ forcingPolicyValue M π f = f := by
    change A *ᵥ (A⁻¹ *ᵥ f) = f
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have h := congrFun he s
  simp only [A, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evaluationPolicyMatrix_mulVec] at h
  linarith

/-- No other real state vector solves that auxiliary Bellman equation. -/
theorem forcingPolicyValue_unique (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f W : State → ℝ)
    (hW : ∀ s, W s = f s + M.discount * (M.policyTransition π s).expectation W) :
    W = forcingPolicyValue M π f := by
  let A : Matrix State State ℝ := 1 - M.discount • evaluationPolicyMatrix M π
  letI : Invertible A := (evaluationPolicyResolvent_isUnit M π).invertible
  have he : f = A *ᵥ W := by
    funext s
    simp only [A, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evaluationPolicyMatrix_mulVec]
    linarith [hW s]
  exact (Matrix.inv_mulVec_eq_vec he).symm

end StatisticalRL.DiscountedMDP

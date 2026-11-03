import Formalization.Generative.PolicyEvaluationVarianceResolvent
import Formalization.Generative.PolicyEvaluationInverse

/-!
# Auxiliary variance values for sharp policy evaluation

The true and empirical auxiliary vectors are the literal finite-matrix
constructions of `eqn:superV-true` and `eqn:superV-hat`. No high-probability
or sharp sample-complexity statement is asserted here.
-/

open scoped Matrix

namespace StatisticalRL.ModelBasedPolicyEvaluation

open StatisticalRL.DiscountedMDP


variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance auxiliaryStateDecidable : DecidableEq State := Classical.decEq State

/-- The source's true auxiliary values. The base case is the actual trajectory value. -/
noncomputable def auxiliaryValue (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : ℕ → State → ℝ
  | 0 => M.trajectoryExpectedValue π
  | l + 1 =>
      (1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
        (fun s ↦ Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π l)))

/-- The source's policy-averaged reward at level zero and successive true
transition standard deviations thereafter. -/
noncomputable def auxiliaryReward (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : ℕ → State → ℝ
  | 0 => M.evaluationPolicyReward π
  | l + 1 => fun s ↦ Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π l))

/-- Each sample-based auxiliary value uses the *same true* auxiliary reward. -/
noncomputable def empiricalAuxiliaryValue (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) (l : ℕ) : State → ℝ :=
  (1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ
    auxiliaryReward M π l

/-- At level zero the literal true resolvent gives the true trajectory value. -/
theorem auxiliaryValue_zero_eq_inverse (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    (1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      auxiliaryReward M π 0 = auxiliaryValue M π 0 := by
  let A : Matrix State State ℝ := 1 - M.discount • evaluationPolicyMatrix M π
  letI : Invertible A := (evaluationPolicyResolvent_isUnit M π).invertible
  apply Matrix.inv_mulVec_eq_vec
  funext s
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evaluationPolicyMatrix_mulVec,
    auxiliaryValue, auxiliaryReward]
  have h := M.evaluationTrajectory_bellman π s
  linarith

/-- Every true auxiliary value has the source's actual inverse representation. -/
theorem auxiliaryValue_eq_inverse (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (l : ℕ) :
    (1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ)⁻¹ *ᵥ
      auxiliaryReward M π l = auxiliaryValue M π l := by
  cases l with
  | zero => exact auxiliaryValue_zero_eq_inverse M π
  | succ l => rfl

/-- The true auxiliary vector satisfies the exact linear Bellman equation. -/
theorem auxiliaryValue_matrix_equation (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (l : ℕ) :
    (1 - M.discount • evaluationPolicyMatrix M π : Matrix State State ℝ) *ᵥ
      auxiliaryValue M π l = auxiliaryReward M π l := by
  let A : Matrix State State ℝ := 1 - M.discount • evaluationPolicyMatrix M π
  letI : Invertible A := (evaluationPolicyResolvent_isUnit M π).invertible
  rw [← auxiliaryValue_eq_inverse M π l]
  change A *ᵥ (A⁻¹ *ᵥ auxiliaryReward M π l) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- The empirical auxiliary vector satisfies the corresponding equation for
its actual sample matrix and the same true reward. -/
theorem empiricalAuxiliaryValue_matrix_equation (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) (l : ℕ) :
    (1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ) *ᵥ
      empiricalAuxiliaryValue M π N hN data l = auxiliaryReward M π l := by
  let A : Matrix State State ℝ := 1 - M.discount • empiricalMatrix N hN data
  letI : Invertible A := (empiricalResolvent_isUnit M N hN data).invertible
  change A *ᵥ (A⁻¹ *ᵥ auxiliaryReward M π l) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- The level-zero empirical auxiliary vector is the actual algorithm's estimator. -/
theorem empiricalAuxiliaryValue_zero (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N) (data : Samples State N) :
    empiricalAuxiliaryValue M π N hN data 0 = valueEstimator M π N hN data := by
  exact valueEstimator_eq_inverse M π N hN data

/-- The auxiliary rewards are nonnegative, including the policy reward at zero. -/
theorem auxiliaryReward_nonneg (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (l : ℕ) (s : State) :
    0 ≤ auxiliaryReward M π l s := by
  cases l with
  | zero => exact (π s).expectation_nonneg (M.reward_nonneg s)
  | succ l => exact Real.sqrt_nonneg _

/-- A true auxiliary value has the standard resolvent sup-norm bound. -/
theorem auxiliaryValue_norm_le_reward (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (l : ℕ) :
    ‖auxiliaryValue M π l‖ ≤ ‖auxiliaryReward M π l‖ / (1 - M.discount) := by
  let V := auxiliaryValue M π l
  let r := auxiliaryReward M π l
  have heq (s : State) : V s = r s + M.discount * (M.policyTransition π s).expectation V := by
    have h := congrFun (auxiliaryValue_matrix_equation M π l) s
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evaluationPolicyMatrix_mulVec] at h
    linarith
  have hbound : ‖V‖ ≤ ‖r‖ + M.discount * ‖V‖ := by
    apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg M.discount_nonneg (norm_nonneg _)))).2
    intro s
    rw [Real.norm_eq_abs, heq s]
    have hr : |r s| ≤ ‖r‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm r s
    have hp : |(M.policyTransition π s).expectation V| ≤ ‖V‖ :=
      (M.policyTransition π s).abs_expectation_le (fun t ↦ by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm V t)
    calc
      _ ≤ |r s| + |M.discount * (M.policyTransition π s).expectation V| := abs_add_le _ _
      _ ≤ ‖r‖ + M.discount * ‖V‖ := by
        rw [abs_mul, abs_of_nonneg M.discount_nonneg]
        exact add_le_add hr (mul_le_mul_of_nonneg_left hp M.discount_nonneg)
  apply (le_div_iff₀ (sub_pos.mpr M.discount_lt_one)).2
  linarith

/-- Each successive auxiliary reward is bounded by the preceding value's norm. -/
theorem auxiliaryReward_succ_norm_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (l : ℕ) :
    ‖auxiliaryReward M π (l + 1)‖ ≤ ‖auxiliaryValue M π l‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro s
  let d := M.policyTransition π s
  let V := auxiliaryValue M π l
  have hv : d.variance V ≤ ‖V‖ ^ 2 := by
    calc
      d.variance V ≤ d.expectation (fun t ↦ V t ^ 2) := d.variance_le_expectation_sq V
      _ ≤ ‖V‖ ^ 2 := d.expectation_le_const (fun t ↦ by
        have hh : |V t| ≤ ‖V‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm V t
        nlinarith [sq_abs (V t), norm_nonneg V, abs_nonneg (V t)])
  change ‖Real.sqrt (d.variance V)‖ ≤ ‖V‖
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hv⟩

/-- Every true auxiliary vector is nonnegative, as needed for the source's
fixed-vector Bernstein family. -/
theorem auxiliaryValue_nonneg (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (l : ℕ) (s : State) :
    0 ≤ auxiliaryValue M π l s := by
  classical
  letI : Nonempty State := M.state_nonempty
  let V := auxiliaryValue M π l
  let r := auxiliaryReward M π l
  obtain ⟨t, _, ht⟩ := Finset.exists_min_image Finset.univ V Finset.univ_nonempty
  have hmin (u : State) : V t ≤ V u := ht u (Finset.mem_univ u)
  have hp : V t ≤ (M.policyTransition π t).expectation V := by
    have h := (M.policyTransition π t).expectation_mono (f := fun _ ↦ V t) (g := V) hmin
    simpa only [FiniteDistribution.expectation_const] using h
  have hr : 0 ≤ r t := auxiliaryReward_nonneg M π l t
  have heq := congrFun (auxiliaryValue_matrix_equation M π l) t
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evaluationPolicyMatrix_mulVec] at heq
  change V t - M.discount * (M.policyTransition π t).expectation V = r t at heq
  have hx : 0 ≤ V t := by
    have hh := mul_le_mul_of_nonneg_left hp M.discount_nonneg
    nlinarith [M.discount_lt_one]
  exact hx.trans (hmin s)

/-- A conservative growth bound for the recursively constructed true vectors.
The source's sharper square-root-horizon estimate requires an additional
variance-resolvent argument and is not claimed here. -/
theorem auxiliaryValue_norm_growth (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (l : ℕ) :
    ‖auxiliaryValue M π l‖ ≤ (1 / (1 - M.discount)) ^ l *
      ‖M.trajectoryExpectedValue π‖ := by
  have hd : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  induction l with
  | zero => simp [auxiliaryValue]
  | succ l ih =>
    calc
      ‖auxiliaryValue M π (l + 1)‖ ≤ ‖auxiliaryReward M π (l + 1)‖ / (1 - M.discount) :=
        auxiliaryValue_norm_le_reward M π (l + 1)
      _ ≤ ‖auxiliaryValue M π l‖ / (1 - M.discount) :=
        div_le_div_of_nonneg_right (auxiliaryReward_succ_norm_le M π l) hd.le
      _ ≤ ((1 / (1 - M.discount)) ^ l * ‖M.trajectoryExpectedValue π‖) / (1 - M.discount) :=
        div_le_div_of_nonneg_right ih hd.le
      _ = (1 / (1 - M.discount)) ^ (l + 1) * ‖M.trajectoryExpectedValue π‖ := by
        rw [pow_succ]
        ring

end StatisticalRL.ModelBasedPolicyEvaluation

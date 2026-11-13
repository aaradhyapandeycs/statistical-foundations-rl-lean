import Formalization.Generative.ModelBasedPolicyEvaluation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Finite-matrix inverse for the empirical policy-evaluation estimator. -/

open scoped BigOperators Matrix

namespace StatisticalRL.ModelBasedPolicyEvaluation

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance inverseStateDecidable : DecidableEq State := Classical.decEq State

/-- The empirical stochastic matrix, with rows indexed by current states. -/
noncomputable def empiricalMatrix (N : ℕ) (hN : 0 < N) (data : Samples State N) :
    Matrix State State ℝ := fun s t ↦ (empiricalPolicyRow N hN data s).prob t

/-- The known state reward induced by the fixed policy. -/
def policyReward (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) :
    State → ℝ := fun s ↦ M.policyExpectedReward π s

theorem empiricalMatrix_mulVec (N : ℕ) (hN : 0 < N) (data : Samples State N)
    (V : State → ℝ) (s : State) :
    (empiricalMatrix N hN data *ᵥ V) s = (empiricalPolicyRow N hN data s).expectation V := by
  rfl

/-- The actual empirical stochastic matrix has an invertible discounted resolvent. -/
theorem empiricalResolvent_isUnit (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) :
    IsUnit (1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hnorm : ‖x - y‖ ≤ M.discount * ‖x - y‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg M.discount_nonneg (norm_nonneg _))).2
    intro s
    have hs := congrFun hxy s
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hs
    rw [empiricalMatrix_mulVec, empiricalMatrix_mulVec] at hs
    have hrow := (empiricalPolicyRow N hN data s).abs_expectation_sub_le
      (f := x) (g := y) (c := ‖x - y‖) (fun t ↦ by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) t)
    rw [Pi.sub_apply, Real.norm_eq_abs]
    have heq : x s - y s = M.discount *
        ((empiricalPolicyRow N hN data s).expectation x -
          (empiricalPolicyRow N hN data s).expectation y) := by linarith
    rw [heq, abs_mul, abs_of_nonneg M.discount_nonneg]
    exact mul_le_mul_of_nonneg_left hrow M.discount_nonneg
  have hz : ‖x - y‖ = 0 := by
    by_contra hn
    have hp : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have hlt := M.discount_lt_one
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- The estimator solves the empirical finite-matrix linear equation. -/
theorem valueEstimator_matrix_equation (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N) (data : Samples State N) :
    (1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ) *ᵥ
      valueEstimator M π N hN data = policyReward M π := by
  funext s
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, empiricalMatrix_mulVec, policyReward,
    DiscountedMDP.policyExpectedReward]
  have h := valueEstimator_bellman M π N hN data s
  linarith

/-- Literal matrix inverse expression for the empirical value estimate. -/
theorem valueEstimator_eq_inverse (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N) (data : Samples State N) :
    (1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ
      policyReward M π = valueEstimator M π N hN data := by
  let A : Matrix State State ℝ := 1 - M.discount • empiricalMatrix N hN data
  letI : Invertible A := (empiricalResolvent_isUnit M N hN data).invertible
  exact Matrix.inv_mulVec_eq_vec (valueEstimator_matrix_equation M π N hN data).symm

end StatisticalRL.ModelBasedPolicyEvaluation

import Formalization.Generative.PolicyEvaluationInverse

/-!
# Order properties of the empirical policy resolvent

These lemmas derive positivity from the actual sampled stochastic rows.
They are deterministic ingredients in the proof of `eq:upper-bound-Vl-Vhatl`.
-/

open scoped Matrix

namespace StatisticalRL.ModelBasedPolicyEvaluation

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance empiricalOrderStateDecidable : DecidableEq State := Classical.decEq State

/-- The empirical inverse applied to a nonnegative vector is nonnegative. -/
theorem empiricalResolvent_mulVec_nonneg (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State N) (f : State → ℝ)
    (hf : ∀ s, 0 ≤ f s) (s : State) :
    0 ≤ ((1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ f) s := by
  classical
  letI : Nonempty State := M.state_nonempty
  let A : Matrix State State ℝ := 1 - M.discount • empiricalMatrix N hN data
  letI : Invertible A := (empiricalResolvent_isUnit M N hN data).invertible
  let u := A⁻¹ *ᵥ f
  have hu : A *ᵥ u = f := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  obtain ⟨t, _, ht⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
  have hmin (v : State) : u t ≤ u v := ht v (Finset.mem_univ v)
  have hp : u t ≤ (empiricalPolicyRow N hN data t).expectation u := by
    have h := (empiricalPolicyRow N hN data t).expectation_mono (f := fun _ ↦ u t)
      (g := u) hmin
    simpa only [FiniteDistribution.expectation_const] using h
  have heq := congrFun hu t
  simp only [A, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, empiricalMatrix_mulVec] at heq
  have htpos : 0 ≤ u t := by
    have hh := mul_le_mul_of_nonneg_left hp M.discount_nonneg
    have hr := hf t
    nlinarith [M.discount_lt_one]
  exact htpos.trans (hmin s)

/-- The empirical inverse is monotone in its input. -/
theorem empiricalResolvent_mulVec_mono (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State N) (f g : State → ℝ)
    (hfg : ∀ s, f s ≤ g s) (s : State) :
    ((1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ f) s ≤
      ((1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ g) s := by
  have h := empiricalResolvent_mulVec_nonneg M N hN data (g - f)
    (fun t ↦ sub_nonneg.mpr (hfg t)) s
  rw [Matrix.mulVec_sub] at h
  simpa only [Pi.sub_apply, sub_nonneg] using h

/-- Applying the empirical inverse to the all-ones vector gives the exact
row-sum factor from `eq:sum-I-minu-gammaP-expand`. -/
theorem empiricalResolvent_mulVec_one (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State N) :
    (1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ
      (fun _ ↦ 1) = (fun _ ↦ 1 / (1 - M.discount)) := by
  let A : Matrix State State ℝ := 1 - M.discount • empiricalMatrix N hN data
  letI : Invertible A := (empiricalResolvent_isUnit M N hN data).invertible
  apply Matrix.inv_mulVec_eq_vec
  funext s
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, empiricalMatrix_mulVec,
    FiniteDistribution.expectation_const]
  have hd : 1 - M.discount ≠ 0 := ne_of_gt (sub_pos.mpr M.discount_lt_one)
  field_simp

/-- The absolute value of the empirical-resolvent image is controlled by
its image of the entrywise absolute value. -/
theorem empiricalResolvent_abs_le (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (data : Samples State N) (f : State → ℝ) (s : State) :
    |((1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ f) s| ≤
      ((1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ
        (fun t ↦ |f t|)) s := by
  have hupper := empiricalResolvent_mulVec_mono M N hN data f (fun t ↦ |f t|)
    (fun t ↦ le_abs_self _) s
  have hlower := empiricalResolvent_mulVec_mono M N hN data (-f) (fun t ↦ |f t|)
    (fun t ↦ neg_le_abs _) s
  rw [Matrix.mulVec_neg] at hlower
  simp only [Pi.neg_apply] at hlower
  exact abs_le.mpr ⟨by linarith, hupper⟩

end StatisticalRL.ModelBasedPolicyEvaluation

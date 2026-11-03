import Formalization.Generative.PolicyEvaluationVarianceResolvent

/-! Generic true-policy inverse positivity and Jensen bridge. -/

open scoped Matrix BigOperators

namespace StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance trueJensenStateDecidable : DecidableEq State := Classical.decEq State

/-- The literal inverse of the true policy transition matrix. -/
noncomputable def truePolicyResolvent (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : Matrix State State ℝ :=
  (1 - M.discount • evaluationPolicyMatrix M π)⁻¹

/-- The actual true-policy resolvent preserves nonnegative vectors. -/
theorem truePolicyResolvent_mulVec_nonneg (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f : State → ℝ) (hf : ∀ s, 0 ≤ f s) (s : State) :
    0 ≤ (truePolicyResolvent M π *ᵥ f) s := by
  classical
  letI : Nonempty State := M.state_nonempty
  let A : Matrix State State ℝ := 1 - M.discount • evaluationPolicyMatrix M π
  letI : Invertible A := (evaluationPolicyResolvent_isUnit M π).invertible
  let u := A⁻¹ *ᵥ f
  have hu : A *ᵥ u = f := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  obtain ⟨t, _, ht⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
  have hmin (v : State) : u t ≤ u v := ht v (Finset.mem_univ v)
  have hp : u t ≤ (M.policyTransition π t).expectation u := by
    have h := (M.policyTransition π t).expectation_mono (f := fun _ ↦ u t) (g := u) hmin
    simpa only [FiniteDistribution.expectation_const] using h
  have heq := congrFun hu t
  simp only [A, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evaluationPolicyMatrix_mulVec] at heq
  have htpos : 0 ≤ u t := by
    have hh := mul_le_mul_of_nonneg_left hp M.discount_nonneg
    have hr := hf t
    nlinarith [M.discount_lt_one]
  exact htpos.trans (hmin s)

/-- Its actual inverse sends the all-one vector to the geometric horizon. -/
theorem truePolicyResolvent_mulVec_one (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    truePolicyResolvent M π *ᵥ (fun _ ↦ 1) = fun _ ↦ 1 / (1 - M.discount) := by
  let A : Matrix State State ℝ := 1 - M.discount • evaluationPolicyMatrix M π
  letI : Invertible A := (evaluationPolicyResolvent_isUnit M π).invertible
  apply Matrix.inv_mulVec_eq_vec
  funext s
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evaluationPolicyMatrix_mulVec,
    FiniteDistribution.expectation_const]
  have hd : 1 - M.discount ≠ 0 := ne_of_gt (sub_pos.mpr M.discount_lt_one)
  field_simp

/-- The true-policy inverse preserves pointwise order. -/
theorem truePolicyResolvent_mulVec_mono (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f g : State → ℝ)
    (hfg : ∀ s, f s ≤ g s) (s : State) :
    (truePolicyResolvent M π *ᵥ f) s ≤ (truePolicyResolvent M π *ᵥ g) s := by
  have h := truePolicyResolvent_mulVec_nonneg M π (g - f)
    (fun t ↦ sub_nonneg.mpr (hfg t)) s
  rw [Matrix.mulVec_sub] at h
  simpa only [Pi.sub_apply, sub_nonneg] using h

/-- Each entry is nonnegative, deduced from the nonnegative inverse image of
an actual coordinate vector. -/
theorem truePolicyResolvent_entry_nonneg (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s t : State) :
    0 ≤ truePolicyResolvent M π s t := by
  have hsingle (r : State) : 0 ≤ (Pi.single t 1 : State → ℝ) r := by
    classical
    by_cases hr : r = t <;> simp [Pi.single_apply, hr]
  have h := truePolicyResolvent_mulVec_nonneg M π (Pi.single t 1) hsingle s
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

/-- The normalized true-resolvent row is a genuine finite probability vector. -/
noncomputable def trueResolventProbabilityRow (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : FiniteDistribution State where
  prob := fun t ↦ (1 - M.discount) * truePolicyResolvent M π s t
  prob_nonneg := fun t ↦ mul_nonneg (sub_pos.mpr M.discount_lt_one).le
    (truePolicyResolvent_entry_nonneg M π s t)
  sum_prob := by
    have hh : 1 - M.discount ≠ 0 := ne_of_gt (sub_pos.mpr M.discount_lt_one)
    have h := congrFun (truePolicyResolvent_mulVec_one M π) s
    simp only [Matrix.mulVec, dotProduct, mul_one] at h
    rw [← Finset.mul_sum, h]
    field_simp

/-- Expectations under the normalized inverse row are the normalized
actual inverse applied to the same vector. -/
theorem trueResolventProbabilityRow_expectation (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) (f : State → ℝ) :
    (trueResolventProbabilityRow M π s).expectation f =
      (1 - M.discount) * (truePolicyResolvent M π *ᵥ f) s := by
  simp only [FiniteDistribution.expectation, trueResolventProbabilityRow,
    Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- Jensen's inequality for the literal true-policy inverse and arbitrary
nonnegative input; no empirical-value special case is assumed. -/
theorem truePolicyResolvent_sqrt_jensen (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (z : State → ℝ) (hz : ∀ s, 0 ≤ z s) (s : State) :
    ((1 - M.discount) * (truePolicyResolvent M π *ᵥ (fun t ↦ Real.sqrt (z t))) s) ^ 2 ≤
      (1 - M.discount) * (truePolicyResolvent M π *ᵥ z) s := by
  let d := trueResolventProbabilityRow M π s
  have h := evaluation_expectation_sq_le d (fun t ↦ Real.sqrt (z t))
  have heq : (fun t ↦ (Real.sqrt (z t)) ^ 2) = z := by
    funext t
    exact Real.sq_sqrt (hz t)
  rw [heq, trueResolventProbabilityRow_expectation, trueResolventProbabilityRow_expectation] at h
  exact h

/-- Uniform norm form used when the nonnegative input is a population variance. -/
theorem truePolicyResolvent_sqrt_norm_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (z : State → ℝ) (hz : ∀ s, 0 ≤ z s) :
    ‖truePolicyResolvent M π *ᵥ (fun t ↦ Real.sqrt (z t))‖ ≤
      Real.sqrt (‖truePolicyResolvent M π *ᵥ z‖ / (1 - M.discount)) := by
  let h := 1 - M.discount
  let U := truePolicyResolvent M π *ᵥ (fun t ↦ Real.sqrt (z t))
  let V := truePolicyResolvent M π *ᵥ z
  have hh : 0 < h := sub_pos.mpr M.discount_lt_one
  have hU (s : State) : 0 ≤ U s := truePolicyResolvent_mulVec_nonneg M π _ (fun _ ↦ Real.sqrt_nonneg _) s
  have hB : 0 ≤ ‖V‖ / h := div_nonneg (norm_nonneg _) hh.le
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro s
  rw [Real.norm_eq_abs, abs_of_nonneg (hU s)]
  apply Real.le_sqrt_of_sq_le
  change (U s) ^ 2 ≤ ‖V‖ / h
  have hj := truePolicyResolvent_sqrt_jensen M π z hz s
  change (h * U s) ^ 2 ≤ h * V s at hj
  have hv : V s ≤ ‖V‖ := (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm V s))
  apply (le_div_iff₀ hh).2
  have hm := mul_le_mul_of_nonneg_left hv hh.le
  have hhbound : h * (h * (U s) ^ 2) ≤ h * ‖V‖ := by nlinarith only [hj, hm]
  have hcancel : h * (U s) ^ 2 ≤ ‖V‖ := le_of_mul_le_mul_left hhbound hh
  nlinarith only [hcancel]

/-- Conditional source-residual bridge: a pointwise nonnegative variance
bound is transported through the actual true-policy inverse. This lemma
assumes the explicitly stated row bound, not its own norm conclusion. -/
theorem truePolicyResolvent_abs_residual_bound (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (f z : State → ℝ) (a b : ℝ)
    (hz : ∀ s, 0 ≤ z s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrow : ∀ s, |f s| ≤ a * Real.sqrt (z s) + b) :
    M.discount * ‖truePolicyResolvent M π *ᵥ (fun s ↦ |f s|)‖ ≤
      M.discount * a * Real.sqrt (‖truePolicyResolvent M π *ᵥ z‖ / (1 - M.discount)) +
        M.discount * b / (1 - M.discount) := by
  let R := truePolicyResolvent M π
  let g : State → ℝ := fun s ↦ Real.sqrt (z s)
  let one : State → ℝ := fun _ ↦ 1
  let U := R *ᵥ (fun s ↦ |f s|)
  have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hU (s : State) : 0 ≤ U s :=
    truePolicyResolvent_mulVec_nonneg M π _ (fun _ ↦ abs_nonneg _) s
  have hRone : R *ᵥ one = fun _ ↦ 1 / (1 - M.discount) :=
    truePolicyResolvent_mulVec_one M π
  have hp (s : State) : U s ≤ a * ‖R *ᵥ g‖ + b / (1 - M.discount) := by
    have hm := truePolicyResolvent_mulVec_mono M π (fun s ↦ |f s|)
      (fun s ↦ a * g s + b) hrow s
    have heq : (fun s ↦ a * g s + b) = a • g + b • one := by
      funext s
      simp [one, smul_eq_mul]
    rw [heq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hRone] at hm
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hm
    have hv : (R *ᵥ g) s ≤ ‖R *ᵥ g‖ := (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (R *ᵥ g) s))
    calc
      _ ≤ a * (R *ᵥ g) s + b * (1 / (1 - M.discount)) := hm
      _ ≤ a * ‖R *ᵥ g‖ + b / (1 - M.discount) := by
        simp only [div_eq_mul_inv, one_mul]
        nlinarith [mul_le_mul_of_nonneg_left hv ha]
  have hnorm : ‖U‖ ≤ a * ‖R *ᵥ g‖ + b / (1 - M.discount) := by
    apply (pi_norm_le_iff_of_nonneg
      (add_nonneg (mul_nonneg ha (norm_nonneg _)) (div_nonneg hb hh.le))).2
    intro s
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hU s)] using hp s
  have hj := truePolicyResolvent_sqrt_norm_le M π z hz
  calc
    _ ≤ M.discount * (a * ‖R *ᵥ g‖ + b / (1 - M.discount)) :=
      mul_le_mul_of_nonneg_left hnorm M.discount_nonneg
    _ ≤ _ := by
      have hmult := mul_le_mul_of_nonneg_left hj ha
      have hmult' := mul_le_mul_of_nonneg_left hmult M.discount_nonneg
      simp only [div_eq_mul_inv] at *
      nlinarith only [hmult']

end StatisticalRL.DiscountedMDP

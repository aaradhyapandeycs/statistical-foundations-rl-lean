import Formalization.Generative.PolicyLearningAbsorbingPreservation

/-! Fixed-parameter stability for the source's absorbing MDP construction.
No statistical independence is asserted for random parameter choices. -/

namespace StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance absorbingLipschitzStateDecidable : DecidableEq State := Classical.decEq State

/-- The absorbing models' optimal Q tables are 1-Lipschitz in their fixed
parameter, despite allowing arbitrary nonabsorbed transitions. -/
theorem absorbingOptimalQ_parameter_lipschitz (M : DiscountedMDP State Action)
    (x : State) (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / (1 - M.discount))
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / (1 - M.discount)) :
    ‖(stateAbsorbingModel M x u hu0 hu1).optimalityFixedPoint -
      (stateAbsorbingModel M x v hv0 hv1).optimalityFixedPoint‖ ≤ |u - v| := by
  let H := stateAbsorbingModel M x u hu0 hu1
  let K := stateAbsorbingModel M x v hv0 hv1
  let Q := H.optimalityFixedPoint
  let R := K.optimalityFixedPoint
  let d := (1 - M.discount) * |u - v|
  have hd : 0 ≤ d := mul_nonneg (sub_pos.mpr M.discount_lt_one).le (abs_nonneg _)
  have htrans : H.transition = K.transition := rfl
  have hdisc : H.discount = K.discount := rfl
  have hreward (s : State) (a : Action) : |H.reward s a - K.reward s a| ≤ d := by
    by_cases hs : s = x
    · subst s
      change |(if x = x then (1 - M.discount) * u else M.reward x a) -
        (if x = x then (1 - M.discount) * v else M.reward x a)| ≤ d
      simp only [↓reduceIte]
      dsimp [d]
      rw [← mul_sub, abs_mul, abs_of_nonneg (sub_pos.mpr M.discount_lt_one).le]
    · change |(if s = x then (1 - M.discount) * u else M.reward s a) -
        (if s = x then (1 - M.discount) * v else M.reward s a)| ≤ d
      simp [hs, hd]
  have hdiff : ‖H.qOptimality R - K.qOptimality R‖ ≤ d := by
    apply (pi_norm_le_iff_of_nonneg hd).2
    intro s
    apply (pi_norm_le_iff_of_nonneg hd).2
    intro a
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    letI : Nonempty Action := M.action_nonempty
    change |H.reward s a + H.discount * (H.transition s a).expectation
      (fun t ↦ actionMaximum (R t)) -
        (K.reward s a + K.discount * (K.transition s a).expectation
          (fun t ↦ actionMaximum (R t)))| ≤ d
    rw [← htrans, ← hdisc, add_sub_add_right_eq_sub]
    exact hreward s a
  have hdecomp : Q - R = (H.qOptimality Q - H.qOptimality R) +
      (H.qOptimality R - K.qOptimality R) := by
    rw [H.optimalityFixedPoint_spec, K.optimalityFixedPoint_spec]
    abel
  have hcon := H.norm_qOptimality_sub_le Q R
  have hbound : ‖Q - R‖ ≤ M.discount * ‖Q - R‖ + d := by
    calc
      ‖Q - R‖ ≤ ‖H.qOptimality Q - H.qOptimality R‖ +
          ‖H.qOptimality R - K.qOptimality R‖ := by
        rw [hdecomp]
        exact norm_add_le _ _
      _ ≤ M.discount * ‖Q - R‖ + d := by
        exact add_le_add hcon hdiff
  have hpos : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  change ‖Q - R‖ ≤ |u - v|
  dsimp [d] at hbound
  nlinarith

/-- The source's fixed-parameter optimal state values are 1-Lipschitz. -/
theorem absorbingOptimalValue_parameter_lipschitz (M : DiscountedMDP State Action)
    (x : State) (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / (1 - M.discount))
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / (1 - M.discount)) :
    ‖optimalTrajectoryValue (stateAbsorbingModel M x u hu0 hu1) -
      optimalTrajectoryValue (stateAbsorbingModel M x v hv0 hv1)‖ ≤ |u - v| := by
  letI : Nonempty Action := M.action_nonempty
  let H := stateAbsorbingModel M x u hu0 hu1
  let K := stateAbsorbingModel M x v hv0 hv1
  have hQ := absorbingOptimalQ_parameter_lipschitz M x u v hu0 hu1 hv0 hv1
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2
  intro s
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [optimalTrajectoryValue_eq_actionMaximum H s, optimalTrajectoryValue_eq_actionMaximum K s]
  apply abs_actionMaximum_sub_le
  intro a
  have hpoint : |H.optimalityFixedPoint s a - K.optimalityFixedPoint s a| ≤
      ‖H.optimalityFixedPoint - K.optimalityFixedPoint‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      (norm_le_pi_norm ((H.optimalityFixedPoint - K.optimalityFixedPoint) s) a).trans
        (norm_le_pi_norm (H.optimalityFixedPoint - K.optimalityFixedPoint) s)
  exact hpoint.trans hQ

/-- Equality holds because the value at the absorbing state is the parameter. -/
theorem absorbingOptimalValue_parameter_norm_eq (M : DiscountedMDP State Action)
    (x : State) (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / (1 - M.discount))
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / (1 - M.discount)) :
    ‖optimalTrajectoryValue (stateAbsorbingModel M x u hu0 hu1) -
      optimalTrajectoryValue (stateAbsorbingModel M x v hv0 hv1)‖ = |u - v| := by
  apply le_antisymm (absorbingOptimalValue_parameter_lipschitz M x u v hu0 hu1 hv0 hv1)
  have h := norm_le_pi_norm (optimalTrajectoryValue (stateAbsorbingModel M x u hu0 hu1) -
    optimalTrajectoryValue (stateAbsorbingModel M x v hv0 hv1)) x
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h
  change |(stateAbsorbingModel M x u hu0 hu1).trajectoryExpectedValue _ x -
    (stateAbsorbingModel M x v hv0 hv1).trajectoryExpectedValue _ x| ≤ _ at h
  rw [stateAbsorbingModel_trajectoryValue_at M x u hu0 hu1,
    stateAbsorbingModel_trajectoryValue_at M x v hv0 hv1] at h
  exact h

end StatisticalRL.ModelBasedPolicyLearning

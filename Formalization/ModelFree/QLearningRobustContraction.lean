import Formalization.ModelFree.QLearningRobustComparator
import Formalization.MDP.FixedPoint

/-! existence and uniqueness for the actual robust operators.
Boundedness of extremal expectation sets is established directly from finite
probability rows; compactness/attainment is not required for contraction. -/
namespace StatisticalRL.QLearning
open StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Every real row expectation is bounded by the finite value sup norm. -/
theorem qRobustExpectations_bounds (p : FiniteDistribution State) (ρ : ℝ) (v : State → ℝ) :
    BddAbove (qRobustExpectations p ρ v) ∧ BddBelow (qRobustExpectations p ρ v) := by
  constructor
  · refine ⟨‖v‖, ?_⟩
    rintro z ⟨q, hq, rfl⟩
    apply (abs_le.mp (q.abs_expectation_le (fun x ↦ ?_))).2
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm v x
  · refine ⟨-‖v‖, ?_⟩
    rintro z ⟨q, hq, rfl⟩
    exact (abs_le.mp (q.abs_expectation_le (fun x ↦ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm v x))).1

/-- Each row's expectation of the action maximum is uniformly nonexpansive. -/
theorem qRobustExpectation_pair_bound (M : DiscountedMDP State Action)
    (q : FiniteDistribution State) (Q R : State → Action → ℝ) :
    |q.expectation (qLearningValue M Q) - q.expectation (qLearningValue M R)| ≤ ‖Q-R‖ := by
  letI : Nonempty Action := M.action_nonempty
  apply q.abs_expectation_sub_le
  intro x
  apply abs_actionMaximum_sub_le
  intro a
  have h : ‖(Q-R) x a‖ ≤ ‖Q-R‖ := (norm_le_pi_norm ((Q-R) x) a).trans (norm_le_pi_norm (Q-R) x)
  simpa [qLearningValue, Real.norm_eq_abs] using h

/-- Supremum and infimum over the same nonempty support-aware χ² ball preserve
the uniform nonexpansive bound. -/
theorem qRobustExtrema_pair_bound (M : DiscountedMDP State Action) (p : FiniteDistribution State)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (Q R : State → Action → ℝ) :
    |sSup (qRobustExpectations p ρ (qLearningValue M Q)) -
      sSup (qRobustExpectations p ρ (qLearningValue M R))| ≤ ‖Q-R‖ ∧
    |sInf (qRobustExpectations p ρ (qLearningValue M Q)) -
      sInf (qRobustExpectations p ρ (qLearningValue M R))| ≤ ‖Q-R‖ := by
  let U := qRobustExpectations p ρ (qLearningValue M Q)
  let V := qRobustExpectations p ρ (qLearningValue M R)
  have hU := qRobustExpectations_nonempty p ρ hρ (qLearningValue M Q)
  have hV := qRobustExpectations_nonempty p ρ hρ (qLearningValue M R)
  have hUb := qRobustExpectations_bounds p ρ (qLearningValue M Q)
  have hVb := qRobustExpectations_bounds p ρ (qLearningValue M R)
  have hpair (q : FiniteDistribution State) := qRobustExpectation_pair_bound M q Q R
  constructor
  · apply abs_le.mpr
    constructor
    · have h : sSup V ≤ sSup U + ‖Q-R‖ := by
        apply csSup_le hV
        rintro z ⟨q, hq, rfl⟩
        have hm : q.expectation (qLearningValue M Q) ≤ sSup U :=
          le_csSup hUb.1 ⟨q,hq,rfl⟩
        linarith [(abs_le.mp (hpair q)).1]
      linarith
    · have h : sSup U ≤ sSup V + ‖Q-R‖ := by
        apply csSup_le hU
        rintro z ⟨q, hq, rfl⟩
        have hm : q.expectation (qLearningValue M R) ≤ sSup V :=
          le_csSup hVb.1 ⟨q,hq,rfl⟩
        linarith [(abs_le.mp (hpair q)).2]
      linarith
  · apply abs_le.mpr
    constructor
    · have h : sInf V - ‖Q-R‖ ≤ sInf U := by
        apply le_csInf hU
        rintro z ⟨q, hq, rfl⟩
        have hm : sInf V ≤ q.expectation (qLearningValue M R) :=
          csInf_le hVb.2 ⟨q,hq,rfl⟩
        linarith [(abs_le.mp (hpair q)).1]
      linarith
    · have h : sInf U - ‖Q-R‖ ≤ sInf V := by
        apply le_csInf hV
        rintro z ⟨q, hq, rfl⟩
        have hm : sInf U ≤ q.expectation (qLearningValue M Q) :=
          csInf_le hUb.2 ⟨q,hq,rfl⟩
        linarith [(abs_le.mp (hpair q)).2]
      linarith

/-- Both source operators are contractions in the actual finite sup norm. -/
theorem qRobustBellman_contracting (M : DiscountedMDP State Action) (ρ b : ℝ) (hρ : 0 ≤ ρ) :
    ContractingWith M.discountConstant (qRobustBellmanPlus M ρ b) ∧
      ContractingWith M.discountConstant (qRobustBellmanMinus M ρ b) := by
  constructor <;> constructor
  all_goals try exact M.discount_lt_one
  all_goals apply LipschitzWith.of_dist_le_mul
  all_goals intro Q R
  all_goals simp only [dist_eq_norm, coe_discountConstant]
  all_goals apply (pi_norm_le_iff_of_nonneg (mul_nonneg M.discount_nonneg (norm_nonneg _))).2
  all_goals intro s
  all_goals apply (pi_norm_le_iff_of_nonneg (mul_nonneg M.discount_nonneg (norm_nonneg _))).2
  all_goals intro a
  all_goals have h := qRobustExtrema_pair_bound M (M.transition s a) ρ hρ Q R
  all_goals simp only [Pi.sub_apply, Real.norm_eq_abs, qRobustBellmanPlus, qRobustBellmanMinus]
  all_goals rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.discount_nonneg]
  · exact mul_le_mul_of_nonneg_left h.1 M.discount_nonneg
  · exact mul_le_mul_of_nonneg_left h.2 M.discount_nonneg

/-- The genuine source operators have unique fixed points; none is assumed. -/
theorem qRobustBellman_fixedPoints_exist_unique (M : DiscountedMDP State Action)
    (ρ b : ℝ) (hρ : 0 ≤ ρ) :
    (∃! Q : State → Action → ℝ, qRobustBellmanPlus M ρ b Q = Q) ∧
      (∃! Q : State → Action → ℝ, qRobustBellmanMinus M ρ b Q = Q) := by
  have h := qRobustBellman_contracting M ρ b hρ
  exact ⟨StatisticalRL.Analysis.contraction_exists_unique h.1,
    StatisticalRL.Analysis.contraction_exists_unique h.2⟩

/- Compactness and attainment are needed for selecting P± and their shifted range; source χ² deviation, stability and the final Q-learning theorem remain separate. -/
end StatisticalRL.QLearning

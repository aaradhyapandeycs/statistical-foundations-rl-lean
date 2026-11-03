import Formalization.Generative.PolicyEvaluationAuxiliary
import Formalization.Generative.PolicyEvaluationEmpiricalResolvent
import Formalization.Generative.EmpiricalResolventOrder

/-! Conditional deterministic residual recursion for the true and empirical
auxiliary values. The pointwise residual hypothesis is an intermediate event,
not a hypothesis of the source's policy-evaluation theorem. -/

open scoped Matrix

namespace StatisticalRL.ModelBasedPolicyEvaluation

open StatisticalRL.DiscountedMDP

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance recursiveStateDecidable : DecidableEq State := Classical.decEq State

/-- The source's exact auxiliary residual identity for each sample. -/
theorem auxiliary_residual_identity (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) (l : ℕ) :
    empiricalAuxiliaryValue M π N hN data l - auxiliaryValue M π l =
      M.discount • ((1 - M.discount • empiricalMatrix N hN data : Matrix State State ℝ)⁻¹ *ᵥ
        ((empiricalMatrix N hN data - evaluationPolicyMatrix M π) *ᵥ auxiliaryValue M π l)) := by
  have h := empirical_true_resolvent_identity M π N hN data (auxiliaryReward M π l)
  rw [auxiliaryValue_eq_inverse] at h
  exact h

/-- Conditional step (i)–(iii) of the source's recursion, with arbitrary
nonnegative rowwise concentration coefficients. -/
theorem auxiliary_residual_recursion_conditional (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (N : ℕ) (hN : 0 < N)
    (data : Samples State N) (l : ℕ) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hres : ∀ s,
      |((empiricalMatrix N hN data - evaluationPolicyMatrix M π) *ᵥ
          auxiliaryValue M π l) s| ≤
        a * Real.sqrt ((M.policyTransition π s).variance (auxiliaryValue M π l)) +
          c * ‖auxiliaryValue M π l‖) :
    ‖empiricalAuxiliaryValue M π N hN data l - auxiliaryValue M π l‖ ≤
      M.discount * a *
        (‖empiricalAuxiliaryValue M π N hN data (l + 1) - auxiliaryValue M π (l + 1)‖ +
          ‖auxiliaryValue M π (l + 1)‖) +
      M.discount * c * ‖auxiliaryValue M π l‖ / (1 - M.discount) := by
  let A : Matrix State State ℝ := 1 - M.discount • empiricalMatrix N hN data
  let R : Matrix State State ℝ := A⁻¹
  let V := auxiliaryValue M π l
  let g : State → ℝ := fun s ↦ Real.sqrt ((M.policyTransition π s).variance V)
  let z := (empiricalMatrix N hN data - evaluationPolicyMatrix M π) *ᵥ V
  let one : State → ℝ := fun _ ↦ 1
  let b : ℝ := c * ‖V‖
  have hb : 0 ≤ b := mul_nonneg hc (norm_nonneg _)
  have hd : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hRone : R *ᵥ one = fun _ ↦ 1 / (1 - M.discount) :=
    empiricalResolvent_mulVec_one M N hN data
  have hRg : R *ᵥ g = empiricalAuxiliaryValue M π N hN data (l + 1) := by rfl
  have hpoint (s : State) : |(R *ᵥ z) s| ≤
      a * ‖empiricalAuxiliaryValue M π N hN data (l + 1)‖ + b / (1 - M.discount) := by
    have hmono := empiricalResolvent_mulVec_mono M N hN data (fun t ↦ |z t|)
      (fun t ↦ a * g t + b) hres s
    have habs := empiricalResolvent_abs_le M N hN data z s
    have heq : (fun t ↦ a * g t + b) = a • g + b • one := by
      funext t
      simp [one, smul_eq_mul]
    rw [heq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hRg, hRone] at hmono
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hmono
    have hn : empiricalAuxiliaryValue M π N hN data (l + 1) s ≤
        ‖empiricalAuxiliaryValue M π N hN data (l + 1)‖ :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (empiricalAuxiliaryValue M π N hN data (l + 1)) s))
    calc
      _ ≤ _ := habs.trans hmono
      _ ≤ _ := by
        simp only [div_eq_mul_inv, one_mul]
        nlinarith [mul_le_mul_of_nonneg_left hn ha]
  have hnorm : ‖R *ᵥ z‖ ≤
      a * ‖empiricalAuxiliaryValue M π N hN data (l + 1)‖ + b / (1 - M.discount) := by
    apply (pi_norm_le_iff_of_nonneg (add_nonneg (mul_nonneg ha (norm_nonneg _)) (div_nonneg hb hd.le))).2
    intro s
    simpa only [Real.norm_eq_abs] using hpoint s
  have htriangle : ‖empiricalAuxiliaryValue M π N hN data (l + 1)‖ ≤
      ‖empiricalAuxiliaryValue M π N hN data (l + 1) - auxiliaryValue M π (l + 1)‖ +
        ‖auxiliaryValue M π (l + 1)‖ := by
    have h := norm_add_le (empiricalAuxiliaryValue M π N hN data (l + 1) -
      auxiliaryValue M π (l + 1)) (auxiliaryValue M π (l + 1))
    simpa only [sub_add_cancel] using h
  rw [auxiliary_residual_identity, norm_smul, Real.norm_eq_abs, abs_of_nonneg M.discount_nonneg]
  calc
    _ ≤ M.discount * (a * ‖empiricalAuxiliaryValue M π N hN data (l + 1)‖ + b / (1 - M.discount)) :=
      mul_le_mul_of_nonneg_left hnorm M.discount_nonneg
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_left htriangle ha
      dsimp [b, V] at *
      simp only [div_eq_mul_inv] at *
      nlinarith [mul_le_mul_of_nonneg_left ht M.discount_nonneg]

end StatisticalRL.ModelBasedPolicyEvaluation

import Formalization.RobustRL.DRVI.Planning
import Formalization.Generative.PolicyLearningVarianceResolventBridge

/-!
# Resolvents of admissible kernels and the comparison principle (milestone 2, module K)

Plan §3.0: for a complete kernel `K` and a deterministic selector `f`, the state kernel is
`s ↦ K s (f s)` and `(I − γK_f)^{-1}` is the library matrix
`truePolicyResolvent (withKernel M K) (detPolicy f)`. Here:
* `kernelResolvent_inverse`: `R ((I − γK_f) z) = z`;
* `le_kernelResolvent`: `x ≤ b + γ K_f x` pointwise implies `x ≤ R b` (comparison);
* monotonicity, nonnegativity, `R 1 = 1/(1-γ)`, and the Jensen norm form are re-exported.
-/

open scoped BigOperators Matrix

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- `(I − γK_f)^{-1}` for the state kernel `s ↦ K s (f s)`. -/
noncomputable def kernelResolvent (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (f : State → Action) :
    Matrix State State ℝ :=
  DiscountedMDP.truePolicyResolvent (withKernel M K) (detPolicy f)

theorem kernelMatrix_mulVec (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (f : State → Action) (v : State → ℝ)
    (s : State) :
    (DiscountedMDP.evaluationPolicyMatrix (withKernel M K) (detPolicy f) *ᵥ v) s =
      (K s (f s)).expectation v := by
  rw [DiscountedMDP.evaluationPolicyMatrix_mulVec,
    HorizonTrap.policyTransition_detPolicy_expectation]
  rfl

/-- `R ((I − γK_f) z) = z`. -/
theorem kernelResolvent_inverse (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (f : State → Action) (z : State → ℝ) :
    kernelResolvent M K f *ᵥ (fun s ↦ z s - M.discount * (K s (f s)).expectation z) = z := by
  classical
  let A : Matrix State State ℝ :=
    1 - (withKernel M K).discount • DiscountedMDP.evaluationPolicyMatrix (withKernel M K)
      (detPolicy f)
  letI : Invertible A :=
    (DiscountedMDP.evaluationPolicyResolvent_isUnit (withKernel M K) (detPolicy f)).invertible
  have hA : (fun s ↦ z s - M.discount * (K s (f s)).expectation z) = A *ᵥ z := by
    funext s
    simp only [A, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, kernelMatrix_mulVec]
    rfl
  rw [hA]
  unfold kernelResolvent DiscountedMDP.truePolicyResolvent
  change A⁻¹ *ᵥ (A *ᵥ z) = z
  rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

theorem kernelResolvent_mono (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (f : State → Action) {u v : State → ℝ}
    (h : ∀ s, u s ≤ v s) (s : State) :
    (kernelResolvent M K f *ᵥ u) s ≤ (kernelResolvent M K f *ᵥ v) s :=
  DiscountedMDP.truePolicyResolvent_mulVec_mono _ _ u v h s

theorem kernelResolvent_nonneg (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (f : State → Action) {u : State → ℝ}
    (h : ∀ s, 0 ≤ u s) (s : State) : 0 ≤ (kernelResolvent M K f *ᵥ u) s :=
  DiscountedMDP.truePolicyResolvent_mulVec_nonneg _ _ u h s

theorem kernelResolvent_const (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (f : State → Action) (c : ℝ) (s : State) :
    (kernelResolvent M K f *ᵥ (fun _ ↦ c)) s = c / (1 - M.discount) := by
  have h1 := congrFun (DiscountedMDP.truePolicyResolvent_mulVec_one (withKernel M K)
    (detPolicy f)) s
  have : (fun _ : State ↦ c) = c • (fun _ : State ↦ (1 : ℝ)) := by funext; simp
  rw [kernelResolvent, this, Matrix.mulVec_smul, Pi.smul_apply, h1, smul_eq_mul]
  change c * (1 / (1 - M.discount)) = c / (1 - M.discount)
  ring

theorem kernelResolvent_add (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (f : State → Action) (u v : State → ℝ)
    (s : State) :
    (kernelResolvent M K f *ᵥ (fun x ↦ u x + v x)) s =
      (kernelResolvent M K f *ᵥ u) s + (kernelResolvent M K f *ᵥ v) s := by
  have : (fun x ↦ u x + v x) = u + v := rfl
  rw [this, Matrix.mulVec_add, Pi.add_apply]

theorem kernelResolvent_smul (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (f : State → Action) (c : ℝ)
    (u : State → ℝ) (s : State) :
    (kernelResolvent M K f *ᵥ (fun x ↦ c * u x)) s = c * (kernelResolvent M K f *ᵥ u) s := by
  have : (fun x ↦ c * u x) = c • u := rfl
  rw [this, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]

/-- Comparison principle: `x ≤ b + γ K_f x` implies `x ≤ (I − γK_f)^{-1} b`. -/
theorem le_kernelResolvent (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (f : State → Action) {x b : State → ℝ}
    (h : ∀ s, x s ≤ b s + M.discount * (K s (f s)).expectation x) (s : State) :
    x s ≤ (kernelResolvent M K f *ᵥ b) s := by
  have hinv := congrFun (kernelResolvent_inverse M K f x) s
  rw [← hinv]
  apply kernelResolvent_mono
  intro t
  linarith [h t]

/-- Jensen, norm form: `‖R √z‖ ≤ √(‖R z‖/(1-γ))` for `z ≥ 0`. -/
theorem kernelResolvent_sqrt_norm_le (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (f : State → Action) (z : State → ℝ)
    (hz : ∀ s, 0 ≤ z s) :
    ‖kernelResolvent M K f *ᵥ (fun t ↦ Real.sqrt (z t))‖ ≤
      Real.sqrt (‖kernelResolvent M K f *ᵥ z‖ / (1 - M.discount)) :=
  DiscountedMDP.truePolicyResolvent_sqrt_norm_le (withKernel M K) (detPolicy f) z hz

end StatisticalRL.RobustRL.DRVI

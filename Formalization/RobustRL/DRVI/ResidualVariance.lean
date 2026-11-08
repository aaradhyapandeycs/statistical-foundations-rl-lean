import Formalization.RobustRL.DRVI.TVSpan

/-!
# One-sided residual total-variance lemma (milestone 2, module V; plan §3.3 "Lemma V")

Let `K` be a complete kernel, `f` a deterministic selector, `Y ≥ 0` with span `≤ B`, and write the
exact residual `e(s) = Y(s) − r(s,f s) − γ⟨K_{s,f s}, Y⟩`. If `e ≤ e⁺` with `e⁺ ≥ 0`, then
`γ² (I−γK_f)^{-1} Var_{K_f}(Y) ≤ 2B/(1−γ) + 2B (I−γK_f)^{-1} e⁺`.
Only an upper bound on the residual is needed (negative residuals help).
-/

open scoped BigOperators Matrix

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem variance_sub_const {Ω : Type*} [Fintype Ω] (d : FiniteDistribution Ω) (f : Ω → ℝ)
    (c : ℝ) : d.variance (fun x ↦ f x - c) = d.variance f := by
  rw [FiniteDistribution.variance_eq_expectation_centered_sq,
    FiniteDistribution.variance_eq_expectation_centered_sq, d.expectation_sub,
    d.expectation_const]
  congr 1
  funext x
  ring

/-- The pointwise step of Lemma V. -/
theorem residual_variance_pointwise {γ r m B e ep y : ℝ} (q : FiniteDistribution State)
    (Y' : State → ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hr : r ≤ 1) (hm : 0 ≤ m)
    (hy0 : 0 ≤ y) (hyB : y ≤ B) (hep : e ≤ ep) (hep0 : 0 ≤ ep)
    (hY : y = r - (1 - γ) * m + γ * q.expectation Y' + e)
    (hsq : 0 ≤ q.expectation (fun x ↦ Y' x ^ 2)) :
    γ ^ 2 * q.variance Y' ≤
      (2 * B + 2 * B * ep) - (y ^ 2 - γ * q.expectation (fun x ↦ Y' x ^ 2)) := by
  set E := q.expectation Y'
  set E2 := q.expectation (fun x ↦ Y' x ^ 2)
  have hvar : q.variance Y' = E2 - E ^ 2 := rfl
  set r' := r - (1 - γ) * m
  have hr' : r' ≤ 1 := by
    have : 0 ≤ (1 - γ) * m := mul_nonneg (by linarith) hm
    simp only [r']; linarith
  have hγE : γ * E = y - (r' + e) := by simp only [r'] at *; linarith
  -- 2 y (r'+e) ≤ 2B(1+ep)
  have hprod : y * (r' + e) ≤ B * (1 + ep) := by
    rcases le_total 0 (r' + e) with h | h
    · have h1 : r' + e ≤ 1 + ep := by linarith
      calc y * (r' + e) ≤ B * (r' + e) := mul_le_mul_of_nonneg_right hyB h
        _ ≤ B * (1 + ep) := mul_le_mul_of_nonneg_left h1 (hy0.trans hyB)
    · have : y * (r' + e) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy0 h
      have : 0 ≤ B * (1 + ep) := mul_nonneg (hy0.trans hyB) (by linarith)
      linarith
  have hγ2 : γ ^ 2 * E2 ≤ γ * E2 := by
    have : γ ^ 2 ≤ γ := by nlinarith
    exact mul_le_mul_of_nonneg_right this hsq
  rw [hvar]
  have : γ ^ 2 * (E2 - E ^ 2) = γ ^ 2 * E2 - (γ * E) ^ 2 := by ring
  rw [this, hγE]
  nlinarith [sq_nonneg (r' + e)]

/-- Lemma V (plan §3.3). -/
theorem residual_variance_bound (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) (f : State → Action)
    (Y ep : State → ℝ) (B : ℝ) (hY0 : ∀ x, 0 ≤ Y x) (hspan : ∀ x y, Y x - Y y ≤ B)
    (he : ∀ s, Y s - M.reward s (f s) - M.discount * (K s (f s)).expectation Y ≤ ep s)
    (hep : ∀ s, 0 ≤ ep s) (s : State) :
    M.discount ^ 2 * (kernelResolvent M K f *ᵥ (fun x ↦ (K x (f x)).variance Y)) s ≤
      2 * B / (1 - M.discount) + 2 * B * (kernelResolvent M K f *ᵥ ep) s := by
  haveI := M.state_nonempty
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  obtain ⟨xm, -, hxm⟩ := Finset.exists_min_image Finset.univ Y Finset.univ_nonempty
  set m := Y xm
  set Y' : State → ℝ := fun x ↦ Y x - m
  set z : State → ℝ := fun x ↦ Y' x ^ 2
  set R := kernelResolvent M K f
  -- pointwise inequality
  have hpt : ∀ x, M.discount ^ 2 * (K x (f x)).variance Y ≤
      (2 * B + 2 * B * ep x) - (z x - M.discount * (K x (f x)).expectation z) := by
    intro x
    have hv : (K x (f x)).variance Y = (K x (f x)).variance Y' := (variance_sub_const _ Y m).symm
    rw [hv]
    have hEY' : (K x (f x)).expectation Y' = (K x (f x)).expectation Y - m := by
      simp only [Y']; rw [(K x (f x)).expectation_sub, (K x (f x)).expectation_const]
    apply residual_variance_pointwise (K x (f x)) Y' hγ0 hγ1.le (M.reward_le_one x (f x))
      (hY0 xm) (y := Y' x) (by simp only [Y']; linarith [hxm x (Finset.mem_univ x)])
      (by simp only [Y']; linarith [hspan x xm]) (e := Y x - M.reward x (f x) -
        M.discount * (K x (f x)).expectation Y) (he x) (hep x)
    · rw [hEY']; simp only [Y']; ring
    · exact (K x (f x)).expectation_nonneg (fun _ ↦ sq_nonneg _)
  have hmono := kernelResolvent_mono M K f hpt s
  -- evaluate the right-hand side
  have hrhs : (R *ᵥ (fun x ↦ (2 * B + 2 * B * ep x) -
      (z x - M.discount * (K x (f x)).expectation z))) s =
      2 * B / (1 - M.discount) + 2 * B * (R *ᵥ ep) s - z s := by
    have hsplit : (fun x ↦ (2 * B + 2 * B * ep x) -
        (z x - M.discount * (K x (f x)).expectation z)) =
        (fun x ↦ 2 * B + 2 * B * ep x) - (fun x ↦ z x - M.discount * (K x (f x)).expectation z) :=
      rfl
    rw [hsplit, Matrix.mulVec_sub, Pi.sub_apply, kernelResolvent_inverse,
      kernelResolvent_add, kernelResolvent_const, kernelResolvent_smul]
  have hlhs : (R *ᵥ (fun x ↦ M.discount ^ 2 * (K x (f x)).variance Y)) s =
      M.discount ^ 2 * (R *ᵥ (fun x ↦ (K x (f x)).variance Y)) s :=
    kernelResolvent_smul M K f _ _ s
  have hz : 0 ≤ z s := sq_nonneg _
  rw [hlhs] at hmono
  rw [hrhs] at hmono
  linarith

end StatisticalRL.RobustRL.DRVI

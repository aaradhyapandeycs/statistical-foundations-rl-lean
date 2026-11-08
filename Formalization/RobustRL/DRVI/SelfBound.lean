import Formalization.RobustRL.DRVI.RowDeviation
import Formalization.RobustRL.DRVI.RobustAbsorbing

/-!
# Decomposition and self-bounding (milestone 5, module B; plan §3.1, §3.7)

* `caseA_le` / `caseB_le`: the error inequalities (ii) and (i) of plan §3.1 through the resolvent
  of a true admissible worst-case kernel.
* `residual_le`: the one-sided residual of the empirical value under that kernel.
* `selfBound`: if `|d(s)| ≤ a1 std_{K_s}(Y) + a0` at every state, then the resolvent-weighted
  deviation `X = ‖R|d|‖` satisfies `X ≤ 2a1√A + a1² D + 2a0/(1−γ)` (plan (★)).
-/

open scoped BigOperators Matrix

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Scalar self-bounding solver. -/
theorem scalar_selfBound {X a1 A D C : ℝ} (hX : 0 ≤ X) (ha1 : 0 ≤ a1) (hA : 0 ≤ A)
    (hD : 0 ≤ D) (_hC : 0 ≤ C) (h : X ≤ a1 * Real.sqrt (A + D * X) + C) :
    X ≤ 2 * a1 * Real.sqrt A + a1 ^ 2 * D + 2 * C := by
  have hDX : 0 ≤ D * X := mul_nonneg hD hX
  have h1 : Real.sqrt (A + D * X) ≤ Real.sqrt A + Real.sqrt (D * X) :=
    sqrt_add_le_add_sqrt' hA hDX
  have h2 : a1 * Real.sqrt (D * X) ≤ (a1 ^ 2 * D + X) / 2 := by
    have hs : a1 * Real.sqrt (D * X) = Real.sqrt (a1 ^ 2 * D * X) := by
      rw [show a1 ^ 2 * D * X = a1 ^ 2 * (D * X) by ring, Real.sqrt_mul (sq_nonneg a1),
        Real.sqrt_sq ha1]
    rw [hs]
    have hu : 0 ≤ a1 ^ 2 * D := mul_nonneg (sq_nonneg a1) hD
    have := Real.sqrt_mul_self (mul_nonneg hu hX)
    have hsq := Real.sq_sqrt (mul_nonneg hu hX)
    nlinarith [sq_nonneg (Real.sqrt (a1 ^ 2 * D * X) - (a1 ^ 2 * D + X) / 2),
      Real.sqrt_nonneg (a1 ^ 2 * D * X), sq_nonneg (a1 ^ 2 * D - X)]
  have h3 : X ≤ a1 * Real.sqrt A + a1 * Real.sqrt (D * X) + C := by
    have := mul_le_mul_of_nonneg_left h1 ha1
    linarith
  linarith

theorem le_norm_self {V : State → ℝ} (s : State) : V s ≤ ‖V‖ :=
  (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm V s)

/-- Case A (plan §3.1 (ii)): `Z − Y ≤ γ R_K |d|`, `K` the true worst kernel at `Y`. -/
theorem caseA_le (U Uh : RowFamily State Action) (hU : ∀ s a, RowAttains (U s a))
    (M Mh : DiscountedMDP State Action) (hr : Mh.reward = M.reward)
    (hγ : Mh.discount = M.discount) (f : State → Action) (s : State) :
    policyFix U M (detPolicy f) s - policyFix Uh Mh (detPolicy f) s ≤
      M.discount * (kernelResolvent M (worstKernel U hU (policyFix Uh Mh (detPolicy f))) f *ᵥ
        (fun t ↦ |rowInf (Uh t (f t)) (policyFix Uh Mh (detPolicy f)) -
          rowInf (U t (f t)) (policyFix Uh Mh (detPolicy f))|)) s := by
  set Y := policyFix Uh Mh (detPolicy f)
  set Z := policyFix U M (detPolicy f)
  set K := worstKernel U hU Y
  have hγ0 := M.discount_nonneg
  have hle : ∀ t, Z t - Y t ≤ M.discount * |rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y| +
      M.discount * (K t (f t)).expectation (fun x ↦ Z x - Y x) := by
    intro t
    have hZ := congrFun (policyFix_spec U M (detPolicy f)) t
    have hY := congrFun (policyFix_spec Uh Mh (detPolicy f)) t
    rw [policyOp_detPolicy] at hZ hY
    rw [hr, hγ] at hY
    have hKZ : rowInf (U t (f t)) Z ≤ (K t (f t)).expectation Z :=
      rowInf_le (worstKernel_mem U hU Y t (f t)) Z
    have hKY : rowInf (U t (f t)) Y = (K t (f t)).expectation Y := worstKernel_spec U hU Y t (f t)
    rw [(K t (f t)).expectation_sub, mul_sub]
    have habs := neg_abs_le (rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y)
    have h1 : M.discount * rowInf (U t (f t)) Z ≤ M.discount * (K t (f t)).expectation Z :=
      mul_le_mul_of_nonneg_left hKZ hγ0
    have h2 : M.discount * (-(|rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y|)) ≤
        M.discount * (rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y) :=
      mul_le_mul_of_nonneg_left habs hγ0
    rw [mul_sub, mul_neg] at h2
    have hKY' : M.discount * rowInf (U t (f t)) Y = M.discount * (K t (f t)).expectation Y := by
      rw [hKY]
    linarith
  have := le_kernelResolvent M K f (x := fun t ↦ Z t - Y t)
    (b := fun t ↦ M.discount * |rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y|) hle s
  rwa [kernelResolvent_smul] at this

/-- Case B (plan §3.1 (i)): with `Y(s) = robustQ Ŭ Y s (f s) + ξ(s)`,
`Y − Z ≤ γ R_K|d| + R_K ξ`, `K` the true worst kernel at `Z = V^{f}`. -/
theorem caseB_le (U Uh : RowFamily State Action) (hU : ∀ s a, RowAttains (U s a))
    (M Mh : DiscountedMDP State Action) (hr : Mh.reward = M.reward)
    (hγ : Mh.discount = M.discount) (f : State → Action) (Y ξ : State → ℝ)
    (hY : ∀ t, Y t = robustQ Uh Mh Y t (f t) + ξ t) (s : State) :
    Y s - policyFix U M (detPolicy f) s ≤
      M.discount * (kernelResolvent M (worstKernel U hU (policyFix U M (detPolicy f))) f *ᵥ
        (fun t ↦ |rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y|)) s +
      (kernelResolvent M (worstKernel U hU (policyFix U M (detPolicy f))) f *ᵥ ξ) s := by
  set Z := policyFix U M (detPolicy f)
  set K := worstKernel U hU Z
  have hγ0 := M.discount_nonneg
  have hle : ∀ t, Y t - Z t ≤ (M.discount * |rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y| +
      ξ t) + M.discount * (K t (f t)).expectation (fun x ↦ Y x - Z x) := by
    intro t
    have hZ := congrFun (policyFix_spec U M (detPolicy f)) t
    rw [policyOp_detPolicy] at hZ
    have hYt := hY t
    unfold robustQ at hYt
    rw [hr, hγ] at hYt
    have hKY : rowInf (U t (f t)) Y ≤ (K t (f t)).expectation Y :=
      rowInf_le (worstKernel_mem U hU Z t (f t)) Y
    have hKZ : rowInf (U t (f t)) Z = (K t (f t)).expectation Z := worstKernel_spec U hU Z t (f t)
    rw [(K t (f t)).expectation_sub, mul_sub]
    have habs := le_abs_self (rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y)
    have h1 : M.discount * rowInf (U t (f t)) Y ≤ M.discount * (K t (f t)).expectation Y :=
      mul_le_mul_of_nonneg_left hKY hγ0
    have h2 : M.discount * (rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y) ≤
        M.discount * |rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y| :=
      mul_le_mul_of_nonneg_left habs hγ0
    rw [mul_sub] at h2
    have hKZ' : M.discount * rowInf (U t (f t)) Z = M.discount * (K t (f t)).expectation Z := by
      rw [hKZ]
    linarith
  have := le_kernelResolvent M K f (x := fun t ↦ Y t - Z t)
    (b := fun t ↦ (M.discount * |rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y|) + ξ t) hle s
  rwa [kernelResolvent_add, kernelResolvent_smul] at this

/-- One-sided residual of the empirical value under an admissible true kernel. -/
theorem residual_le (U Uh : RowFamily State Action) (M Mh : DiscountedMDP State Action)
    (hr : Mh.reward = M.reward) (hγ : Mh.discount = M.discount) (f : State → Action)
    (K : State → Action → FiniteDistribution State) (hK : ∀ s a, K s a ∈ U s a)
    (Y ξ : State → ℝ) (hY : ∀ t, Y t = robustQ Uh Mh Y t (f t) + ξ t) (t : State) :
    Y t - M.reward t (f t) - M.discount * (K t (f t)).expectation Y ≤
      M.discount * |rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y| + ξ t := by
  have hYt := hY t
  unfold robustQ at hYt
  rw [hr, hγ] at hYt
  have hKY : rowInf (U t (f t)) Y ≤ (K t (f t)).expectation Y := rowInf_le (hK t (f t)) Y
  have habs := le_abs_self (rowInf (Uh t (f t)) Y - rowInf (U t (f t)) Y)
  have h1 := mul_le_mul_of_nonneg_left hKY M.discount_nonneg
  have h2 := mul_le_mul_of_nonneg_left habs M.discount_nonneg
  linarith

/-- Self-bounding (plan (★)). -/
theorem selfBound (M : DiscountedMDP State Action) (K : State → Action → FiniteDistribution State)
    (f : State → Action) (Y d ξ : State → ℝ) {B' Ξ a1 a0 : ℝ}
    (hγpos : 0 < M.discount) (hY0 : ∀ x, 0 ≤ Y x) (hspan : ∀ x y, Y x - Y y ≤ B')
    (hres : ∀ t, Y t - M.reward t (f t) - M.discount * (K t (f t)).expectation Y ≤
      M.discount * |d t| + ξ t)
    (hξ0 : ∀ t, 0 ≤ ξ t) (hξΞ : ∀ t, ξ t ≤ Ξ) (ha1 : 0 ≤ a1) (ha0 : 0 ≤ a0)
    (hd : ∀ t, |d t| ≤ a1 * Real.sqrt ((K t (f t)).variance Y) + a0) :
    ‖kernelResolvent M K f *ᵥ (fun t ↦ |d t|)‖ ≤
      2 * a1 * Real.sqrt (2 * B' * (1 + Ξ) / (M.discount ^ 2 * (1 - M.discount) ^ 2)) +
        a1 ^ 2 * (2 * B' / (M.discount * (1 - M.discount))) + 2 * (a0 / (1 - M.discount)) := by
  haveI := M.state_nonempty
  set γ := M.discount with hγdef
  set R := kernelResolvent M K f
  set X := ‖R *ᵥ (fun t ↦ |d t|)‖
  set v : State → ℝ := fun t ↦ (K t (f t)).variance Y
  have hγ1 : γ < 1 := M.discount_lt_one
  have hpos : 0 < 1 - γ := by linarith
  have hB' : 0 ≤ B' := by
    obtain ⟨x⟩ := (inferInstance : Nonempty State); have := hspan x x; linarith
  have hΞ : 0 ≤ Ξ := by
    obtain ⟨x⟩ := (inferInstance : Nonempty State); exact (hξ0 x).trans (hξΞ x)
  have hX0 : 0 ≤ X := norm_nonneg _
  have hv0 : ∀ t, 0 ≤ v t := fun t ↦ FiniteDistribution.variance_nonneg _ _
  -- R ξ ≤ Ξ/(1−γ)
  have hRξ : ∀ t, (R *ᵥ ξ) t ≤ Ξ / (1 - γ) := by
    intro t
    have := kernelResolvent_mono M K f (u := ξ) (v := fun _ ↦ Ξ) hξΞ t
    rwa [kernelResolvent_const] at this
  -- Lemma V
  have hRv : ∀ t, (R *ᵥ v) t ≤ (2 * B' * (1 + Ξ) / (1 - γ) + 2 * B' * γ * X) / γ ^ 2 := by
    intro t
    have hV := residual_variance_bound M K f Y (fun t ↦ γ * |d t| + ξ t) B' hY0 hspan hres
      (fun t ↦ add_nonneg (mul_nonneg M.discount_nonneg (abs_nonneg _)) (hξ0 t)) t
    have hsplit : (R *ᵥ (fun t ↦ γ * |d t| + ξ t)) t =
        γ * (R *ᵥ (fun t ↦ |d t|)) t + (R *ᵥ ξ) t := by
      rw [kernelResolvent_add, kernelResolvent_smul]
    change γ ^ 2 * (R *ᵥ v) t ≤ 2 * B' / (1 - γ) + 2 * B' * (R *ᵥ fun t ↦ γ * |d t| + ξ t) t at hV
    rw [hsplit] at hV
    have hdX : (R *ᵥ (fun t ↦ |d t|)) t ≤ X := le_norm_self t
    have h1 : 2 * B' * (γ * (R *ᵥ fun t ↦ |d t|) t + (R *ᵥ ξ) t) ≤
        2 * B' * (γ * X + Ξ / (1 - γ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hdX M.discount_nonneg) (hRξ t)
    rw [le_div_iff₀ (by positivity)]
    have e : 2 * B' * (1 + Ξ) / (1 - γ) + 2 * B' * γ * X =
        2 * B' / (1 - γ) + 2 * B' * (γ * X + Ξ / (1 - γ)) := by
      field_simp; ring
    rw [e]; nlinarith
  have hRvnorm : ‖R *ᵥ v‖ ≤ (2 * B' * (1 + Ξ) / (1 - γ) + 2 * B' * γ * X) / γ ^ 2 := by
    apply norm_le_of_abs_le (by positivity)
    intro t
    rw [abs_of_nonneg (kernelResolvent_nonneg M K f hv0 t)]
    exact hRv t
  -- the deviation through the resolvent
  have hRd : ∀ t, (R *ᵥ (fun t ↦ |d t|)) t ≤
      a1 * ‖R *ᵥ (fun t ↦ Real.sqrt (v t))‖ + a0 / (1 - γ) := by
    intro t
    have hm := kernelResolvent_mono M K f (u := fun t ↦ |d t|)
      (v := fun t ↦ a1 * Real.sqrt (v t) + a0) hd t
    rw [kernelResolvent_add, kernelResolvent_smul, kernelResolvent_const] at hm
    have := le_norm_self (V := R *ᵥ (fun t ↦ Real.sqrt (v t))) t
    have := mul_le_mul_of_nonneg_left this ha1
    linarith
  have hjensen := kernelResolvent_sqrt_norm_le M K f v hv0
  have hXle : X ≤ a1 * Real.sqrt ((2 * B' * (1 + Ξ) / (γ ^ 2 * (1 - γ) ^ 2)) +
      (2 * B' / (γ * (1 - γ))) * X) + a0 / (1 - γ) := by
    have hXt : X ≤ a1 * ‖R *ᵥ (fun t ↦ Real.sqrt (v t))‖ + a0 / (1 - γ) := by
      apply norm_le_of_abs_le (by positivity)
      intro t
      rw [abs_of_nonneg (kernelResolvent_nonneg M K f (fun _ ↦ abs_nonneg _) t)]
      exact hRd t
    have hroot : ‖R *ᵥ (fun t ↦ Real.sqrt (v t))‖ ≤
        Real.sqrt ((2 * B' * (1 + Ξ) / (γ ^ 2 * (1 - γ) ^ 2)) +
          (2 * B' / (γ * (1 - γ))) * X) := by
      refine hjensen.trans (Real.sqrt_le_sqrt ?_)
      have e : (2 * B' * (1 + Ξ) / (γ ^ 2 * (1 - γ) ^ 2)) + (2 * B' / (γ * (1 - γ))) * X =
          ((2 * B' * (1 + Ξ) / (1 - γ) + 2 * B' * γ * X) / γ ^ 2) / (1 - γ) := by
        field_simp
      rw [e]
      exact div_le_div_of_nonneg_right hRvnorm hpos.le
    have := mul_le_mul_of_nonneg_left hroot ha1
    linarith
  have hA : 0 ≤ 2 * B' * (1 + Ξ) / (γ ^ 2 * (1 - γ) ^ 2) := by positivity
  have hD : 0 ≤ 2 * B' / (γ * (1 - γ)) := by positivity
  exact scalar_selfBound hX0 ha1 hA hD (by positivity) hXle

end StatisticalRL.RobustRL.DRVI

import Formalization.ModelFree.FiniteQ.Comparators

/-! # Distance of the comparison functions to `Q⋆` (finite-horizon stability)

Deterministic replacement of the KL/Pinsker step `B.2(ii′)` of the paper proof in
`CHECK-Thm4_12-4_13.md`. For every stage list of length at most `K`,
`0 ≤ Q⁺ - Q⋆ ≤ D` and `0 ≤ Q⋆ - Q⁻ ≤ D` whenever `K (b + √(2ρ) D + ρ/(2λ)) + λ K² ≤ D`.

The proof is a backward induction with the potential `Ψ = 2K V⋆ - (V⋆)²` (a total-variance
argument): `Var_{P_h}(V⋆_{h+1}) ≤ Ψ'_h - P_h Ψ_{h+1}` with `Ψ'_h = 2K Q⋆_h - (Q⋆_h)²`, the χ²
deviation `sup_{q ∈ U_ρ(p)} q V - p V ≤ √(ρ Var_p V)` (`qRobustExpectations_sSup_sub_le`), the
perturbation `Var(V^±) ≤ 2 Var(V⋆) + 2 D²`, and `√(2ρ v) ≤ λ v + ρ/(2λ)`. -/

open StatisticalRL.QLearning

namespace StatisticalRL.FiniteQLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

open EnvironmentStage

/-! ## Elementary finite-distribution facts -/

theorem variance_add_le (p : FiniteDistribution State) (f g : State → ℝ) :
    p.variance (fun x ↦ f x + g x) ≤ 2 * p.variance f + 2 * p.variance g := by
  have hE : p.expectation (fun x ↦ f x + g x) = p.expectation f + p.expectation g :=
    p.expectation_add f g
  rw [p.variance_eq_expectation_centered_sq, p.variance_eq_expectation_centered_sq,
    p.variance_eq_expectation_centered_sq, hE]
  have h1 := p.expectation_mul 2 (fun x ↦ (f x - p.expectation f) ^ 2)
  have h2 := p.expectation_mul 2 (fun x ↦ (g x - p.expectation g) ^ 2)
  have h3 := p.expectation_add (fun x ↦ 2 * (f x - p.expectation f) ^ 2)
    (fun x ↦ 2 * (g x - p.expectation g) ^ 2)
  rw [← h1, ← h2, ← h3]
  apply p.expectation_mono
  intro x
  nlinarith [sq_nonneg ((f x - p.expectation f) - (g x - p.expectation g))]

theorem variance_le_of_abs_le (p : FiniteDistribution State) (d : State → ℝ) {D : ℝ}
    (h : ∀ x, |d x| ≤ D) : p.variance d ≤ D ^ 2 := by
  refine (p.variance_le_expectation_sq d).trans (p.expectation_le_const fun x ↦ ?_)
  have := h x
  have h0 := abs_nonneg (d x)
  nlinarith [sq_abs (d x)]

/-- `√(ρ Var W) ≤ λ Var V + ρ/(2λ) + √(2ρ) D` when `|W - V| ≤ D`. -/
theorem sqrt_variance_perturb_le (p : FiniteDistribution State) (V W : State → ℝ) {ρ lam D : ℝ}
    (hρ : 0 ≤ ρ) (hlam : 0 < lam) (hD : 0 ≤ D) (h : ∀ x, |W x - V x| ≤ D) :
    Real.sqrt (ρ * p.variance W) ≤
      lam * p.variance V + ρ / (2 * lam) + Real.sqrt (2 * ρ) * D := by
  have hW : W = fun x ↦ V x + (W x - V x) := by funext x; ring
  have hvar : p.variance W ≤ 2 * p.variance V + 2 * D ^ 2 := by
    have h1 := variance_add_le p V (fun x ↦ W x - V x)
    have h2 := variance_le_of_abs_le p (fun x ↦ W x - V x) h
    rw [← hW] at h1
    linarith
  set a := p.variance V with ha
  have ha0 : 0 ≤ a := p.variance_nonneg V
  set c := ρ / (2 * lam) with hc
  have hc2 : 2 * lam * c = ρ := by rw [hc]; field_simp
  have hc0 : 0 ≤ c := by positivity
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * ρ by linarith)
  have hs0 := Real.sqrt_nonneg (2 * ρ)
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hρW : ρ * p.variance W ≤ ρ * (2 * a + 2 * D ^ 2) := mul_le_mul_of_nonneg_left hvar hρ
  nlinarith [sq_nonneg (lam * a - c), mul_nonneg (mul_nonneg hs0 hD) (add_nonneg
    (mul_nonneg hlam.le ha0) hc0)]

/-! ## The total-variance potential -/

/-- `Ψ = 2K V⋆ - (V⋆)²`. -/
noncomputable def psiV (K : ℝ) (es : List (EnvironmentStage State Action)) (s : State) : ℝ :=
  2 * K * optimalValue es s - optimalValue es s ^ 2

/-- `Ψ' = 2K Q⋆ - (Q⋆)²`. -/
noncomputable def psiQ (K : ℝ) (es : List (EnvironmentStage State Action)) (s : State)
    (a : Action) : ℝ :=
  2 * K * optimalQ es s a - optimalQ es s a ^ 2

theorem psiQ_le_sq (K : ℝ) (es : List (EnvironmentStage State Action)) (s : State) (a : Action) :
    psiQ K es s a ≤ K ^ 2 := by
  unfold psiQ
  nlinarith [sq_nonneg (K - optimalQ es s a)]

theorem psiQ_le_psiV [Nonempty Action] {K : ℝ} (es : List (EnvironmentStage State Action))
    (hlen : (es.length : ℝ) ≤ K) (s : State) (a : Action) : psiQ K es s a ≤ psiV K es s := by
  unfold psiQ psiV
  have h1 := optimalQ_le_optimalValue es s a
  have h2 := (optimalValue_mem_range es s).2
  nlinarith

/-- One-step total-variance inequality: `Var_P(V⋆_{h+1}) ≤ Ψ'_h - P Ψ_{h+1}`. -/
theorem variance_le_psi {K : ℝ} (e : EnvironmentStage State Action)
    (es : List (EnvironmentStage State Action)) (hlen : (es.length : ℝ) + 1 ≤ K)
    (s : State) (a : Action) :
    (e.transition s a).variance (optimalValue es) ≤
      psiQ K (e :: es) s a - (e.transition s a).expectation (psiV K es) := by
  set p := e.transition s a
  set V := optimalValue es
  have hE : p.expectation (psiV K es) = 2 * K * p.expectation V - p.expectation (fun x ↦ V x ^ 2) := by
    unfold psiV
    rw [p.expectation_sub, p.expectation_mul]
  have hQ : optimalQ (e :: es) s a = e.reward s a + p.expectation V := rfl
  have hV : ∀ x, 0 ≤ V x ∧ V x ≤ es.length := fun x ↦ by
    letI : Nonempty Action := e.action_nonempty
    exact optimalValue_mem_range es x
  have hm1 : p.expectation V ≤ es.length := p.expectation_le_const fun x ↦ (hV x).2
  have hr0 := e.reward_nonneg s a
  have hr1 := e.reward_le_one s a
  rw [FiniteDistribution.variance, hE]
  unfold psiQ
  rw [hQ]
  nlinarith [mul_nonneg hr0 (show 0 ≤ 2 * K - e.reward s a - 2 * p.expectation V by linarith)]

/-! ## Stability of the comparison functions -/

section Stability

variable [Nonempty Action]

theorem plusV_sub_optimalValue_le {ρ b : ℝ} (es : List (EnvironmentStage State Action)) (s : State)
    {F : State → Action → ℝ} (h : ∀ a, plusQ ρ b es s a - optimalQ es s a ≤ F s a) :
    plusV ρ b es s - optimalValue es s ≤ actionMaximum (F s) := by
  rw [plusV_eq, optimalValue_eq]
  exact (actionMaximum_sub_le _ _).trans (actionMaximum_le_of_forall fun a ↦
    (h a).trans (le_actionMaximum _ a))

/-- Upper comparison: `0 ≤ Q⁺ - Q⋆ ≤ n c₀ + λ Ψ'` for a list of length `n ≤ K`, where
`c₀ = b + √(2ρ) D + ρ/(2λ)`. -/
theorem plusQ_sub_optimalQ_le {ρ b lam D K : ℝ} (hρ : 0 ≤ ρ) (hb : 0 ≤ b) (hlam : 0 < lam)
    (hD0 : 0 ≤ D) (hD : K * (b + Real.sqrt (2 * ρ) * D + ρ / (2 * lam)) + lam * K ^ 2 ≤ D) :
    ∀ es : List (EnvironmentStage State Action), (es.length : ℝ) ≤ K → ∀ s a,
      0 ≤ plusQ ρ b es s a - optimalQ es s a ∧
      plusQ ρ b es s a - optimalQ es s a ≤
        es.length * (b + Real.sqrt (2 * ρ) * D + ρ / (2 * lam)) + lam * psiQ K es s a := by
  set c₀ := b + Real.sqrt (2 * ρ) * D + ρ / (2 * lam) with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  intro es
  induction es with
  | nil => intro _ s a; simp [plusQ, optimalQ, psiQ]
  | cons e xs ih =>
    intro hlen s a
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hlen ⊢
    have hxs : (xs.length : ℝ) ≤ K := by linarith
    have ih' := ih hxs
    set p := e.transition s a
    set Vp := plusV ρ b xs
    set Vs := optimalValue xs
    -- value differences at the next stage
    have hdiff : ∀ x, 0 ≤ Vp x - Vs x ∧ Vp x - Vs x ≤ xs.length * c₀ + lam * psiV K xs x ∧
        Vp x - Vs x ≤ D := by
      intro x
      have hup := plusV_sub_optimalValue_le (ρ := ρ) (b := b) xs x
        (F := fun x a ↦ xs.length * c₀ + lam * psiV K xs x)
        (fun a ↦ (ih' x a).2.trans (by
          have := psiQ_le_psiV xs hxs x a
          nlinarith))
      rw [actionMaximum_const'] at hup
      have hlow : Vs x ≤ Vp x := by
        simp only [Vs, Vp]
        rw [plusV_eq, optimalValue_eq]
        exact actionMaximum_le_of_forall fun a ↦ le_trans (b := plusQ ρ b xs x a)
          (by linarith [(ih' x a).1]) (le_actionMaximum _ a)
      obtain ⟨a0, -, ha0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (plusQ ρ b xs x)
      have hD' : Vp x - Vs x ≤ D := by
        have hmax : Vp x - Vs x ≤ actionMaximum (fun a ↦ plusQ ρ b xs x a - optimalQ xs x a) := by
          simp only [Vp, Vs]
          rw [plusV_eq, optimalValue_eq]
          exact actionMaximum_sub_le _ _
        refine hmax.trans (actionMaximum_le_of_forall fun a ↦ (ih' x a).2.trans ?_)
        have h1 := psiQ_le_sq K xs x a
        have h2 : (xs.length : ℝ) * c₀ ≤ K * c₀ := mul_le_mul_of_nonneg_right hxs hc₀0
        nlinarith
      exact ⟨by linarith, hup, hD'⟩
    have hsup := qRobustExpectations_sSup_sub_le p ρ hρ Vp
    have hpert := sqrt_variance_perturb_le p Vs Vp hρ hlam hD0 fun x ↦ by
      rw [abs_le]; constructor <;> linarith [(hdiff x).1, (hdiff x).2.2]
    have hmean : p.expectation Vp - p.expectation Vs ≤ xs.length * c₀ +
        lam * p.expectation (psiV K xs) := by
      rw [← p.expectation_sub, ← p.expectation_mul]
      have := p.expectation_mono (f := fun x ↦ Vp x - Vs x)
        (g := fun x ↦ xs.length * c₀ + lam * psiV K xs x) fun x ↦ (hdiff x).2.1
      rwa [p.expectation_add, p.expectation_const] at this
    have hmean0 : 0 ≤ p.expectation Vp - p.expectation Vs := by
      rw [← p.expectation_sub]
      exact p.expectation_nonneg fun x ↦ (hdiff x).1
    have hvar := variance_le_psi (K := K) e xs (by linarith) s a
    have hge := expectation_le_sSup_robust p hρ Vp
    have heq : plusQ ρ b (e :: xs) s a - optimalQ (e :: xs) s a =
        b + (sSup (qRobustExpectations p ρ Vp) - p.expectation Vp) +
          (p.expectation Vp - p.expectation Vs) := by
      simp only [plusQ, optimalQ, qBackup, p, Vp, Vs]
      ring
    rw [heq]
    constructor
    · linarith
    · have hlamvar := mul_le_mul_of_nonneg_left hvar hlam.le
      nlinarith

/-- Lower comparison: `0 ≤ Q⋆ - Q⁻ ≤ n c₀ + λ Ψ'`. -/
theorem optimalQ_sub_minusQ_le {ρ b lam D K : ℝ} (hρ : 0 ≤ ρ) (hb : 0 ≤ b) (hlam : 0 < lam)
    (hD0 : 0 ≤ D) (hD : K * (b + Real.sqrt (2 * ρ) * D + ρ / (2 * lam)) + lam * K ^ 2 ≤ D) :
    ∀ es : List (EnvironmentStage State Action), (es.length : ℝ) ≤ K → ∀ s a,
      0 ≤ optimalQ es s a - minusQ ρ b es s a ∧
      optimalQ es s a - minusQ ρ b es s a ≤
        es.length * (b + Real.sqrt (2 * ρ) * D + ρ / (2 * lam)) + lam * psiQ K es s a := by
  set c₀ := b + Real.sqrt (2 * ρ) * D + ρ / (2 * lam) with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  intro es
  induction es with
  | nil => intro _ s a; simp [minusQ, optimalQ, psiQ]
  | cons e xs ih =>
    intro hlen s a
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hlen ⊢
    have hxs : (xs.length : ℝ) ≤ K := by linarith
    have ih' := ih hxs
    set p := e.transition s a
    set Vm := minusV ρ b xs
    set Vs := optimalValue xs
    have hdiff : ∀ x, 0 ≤ Vs x - Vm x ∧ Vs x - Vm x ≤ xs.length * c₀ + lam * psiV K xs x ∧
        Vs x - Vm x ≤ D := by
      intro x
      have hmax : Vs x - Vm x ≤ actionMaximum (fun a ↦ optimalQ xs x a - minusQ ρ b xs x a) := by
        simp only [Vm, Vs]
        rw [minusV_eq, optimalValue_eq]
        exact actionMaximum_sub_le _ _
      have hup : Vs x - Vm x ≤ xs.length * c₀ + lam * psiV K xs x :=
        hmax.trans (actionMaximum_le_of_forall fun a ↦ (ih' x a).2.trans (by
          have := psiQ_le_psiV xs hxs x a
          nlinarith))
      have hlow : Vm x ≤ Vs x := by
        simp only [Vs, Vm]
        rw [minusV_eq, optimalValue_eq]
        exact actionMaximum_le_of_forall fun a ↦ le_trans (b := optimalQ xs x a)
          (by linarith [(ih' x a).1]) (le_actionMaximum _ a)
      have hD' : Vs x - Vm x ≤ D := by
        refine hmax.trans (actionMaximum_le_of_forall fun a ↦ (ih' x a).2.trans ?_)
        have h1 := psiQ_le_sq K xs x a
        have h2 : (xs.length : ℝ) * c₀ ≤ K * c₀ := mul_le_mul_of_nonneg_right hxs hc₀0
        nlinarith
      exact ⟨by linarith, hup, hD'⟩
    have hinf := expectation_sub_sInf_le p hρ Vm
    have hpert := sqrt_variance_perturb_le p Vs Vm hρ hlam hD0 fun x ↦ by
      rw [abs_le]; constructor <;> linarith [(hdiff x).1, (hdiff x).2.2]
    have hmean : p.expectation Vs - p.expectation Vm ≤ xs.length * c₀ +
        lam * p.expectation (psiV K xs) := by
      rw [← p.expectation_sub, ← p.expectation_mul]
      have := p.expectation_mono (f := fun x ↦ Vs x - Vm x)
        (g := fun x ↦ xs.length * c₀ + lam * psiV K xs x) fun x ↦ (hdiff x).2.1
      rwa [p.expectation_add, p.expectation_const] at this
    have hmean0 : 0 ≤ p.expectation Vs - p.expectation Vm := by
      rw [← p.expectation_sub]
      exact p.expectation_nonneg fun x ↦ (hdiff x).1
    have hvar := variance_le_psi (K := K) e xs (by linarith) s a
    have hle := sInf_robust_le_expectation p hρ Vm
    have heq : optimalQ (e :: xs) s a - minusQ ρ b (e :: xs) s a =
        b + (p.expectation Vm - sInf (qRobustExpectations p ρ Vm)) +
          (p.expectation Vs - p.expectation Vm) := by
      simp only [minusQ, optimalQ, qBackup, p, Vm, Vs]
      ring
    rw [heq]
    constructor
    · linarith
    · have hlamvar := mul_le_mul_of_nonneg_left hvar hlam.le
      nlinarith

/-- Packaged stability: `0 ≤ Q⁺ - Q⋆ ≤ D` and `0 ≤ Q⋆ - Q⁻ ≤ D` for every list of length at most
`K`. -/
theorem comparators_near_optimal {ρ b lam D K : ℝ} (hρ : 0 ≤ ρ) (hb : 0 ≤ b) (hlam : 0 < lam)
    (hD0 : 0 ≤ D) (hD : K * (b + Real.sqrt (2 * ρ) * D + ρ / (2 * lam)) + lam * K ^ 2 ≤ D)
    (es : List (EnvironmentStage State Action)) (hlen : (es.length : ℝ) ≤ K) (s : State)
    (a : Action) :
    (0 ≤ plusQ ρ b es s a - optimalQ es s a ∧ plusQ ρ b es s a - optimalQ es s a ≤ D) ∧
    (0 ≤ optimalQ es s a - minusQ ρ b es s a ∧ optimalQ es s a - minusQ ρ b es s a ≤ D) := by
  have hc₀0 : 0 ≤ b + Real.sqrt (2 * ρ) * D + ρ / (2 * lam) := by positivity
  have h2 : (es.length : ℝ) * (b + Real.sqrt (2 * ρ) * D + ρ / (2 * lam)) ≤
      K * (b + Real.sqrt (2 * ρ) * D + ρ / (2 * lam)) := mul_le_mul_of_nonneg_right hlen hc₀0
  have h1 := mul_le_mul_of_nonneg_left (psiQ_le_sq K es s a) hlam.le
  have hp := plusQ_sub_optimalQ_le hρ hb hlam hD0 hD es hlen s a
  have hm := optimalQ_sub_minusQ_le hρ hb hlam hD0 hD es hlen s a
  exact ⟨⟨hp.1, by linarith [hp.2]⟩, ⟨hm.1, by linarith [hm.2]⟩⟩

end Stability

end StatisticalRL.FiniteQLearning

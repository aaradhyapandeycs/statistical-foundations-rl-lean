import Formalization.RobustRL.DRVI.LooFamily

/-!
# Deterministic gap bound for DRVI (milestone 5; plan §3.1 + §3.7)

For any data set and any greedy selector `f̂` of the DRVI iterate `Q̂_T`, if at every state the
row deviations of the two empirical values `Y_A = V̂^{π⋆}` and `Y_B = V̂⋆` are bounded by
`a1 · std_q(Y) + a0` for every admissible row `q` of the true ball, then
`V^{⋆,σ}(s) − V^{π̂,σ}(s) ≤ 2 Xb + Ξ/(1−γ)`, where `Xb` is the self-bounding expression and
`Ξ ≥ 2γ^T/(1−γ)` bounds the planning residual.
-/

open scoped BigOperators Matrix

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7
open StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The self-bounding expression of plan (★). -/
noncomputable def selfBoundExpr (γ B' Ξ a1 a0 : ℝ) : ℝ :=
  2 * a1 * Real.sqrt (2 * B' * (1 + Ξ) / (γ ^ 2 * (1 - γ) ^ 2)) +
    a1 ^ 2 * (2 * B' / (γ * (1 - γ))) + 2 * (a0 / (1 - γ))

theorem selfBoundExpr_mono_Ξ {γ B' Ξ Ξ' a1 a0 : ℝ} (hB' : 0 ≤ B') (ha1 : 0 ≤ a1)
    (hΞ : Ξ ≤ Ξ') : selfBoundExpr γ B' Ξ a1 a0 ≤ selfBoundExpr γ B' Ξ' a1 a0 := by
  unfold selfBoundExpr
  have : Real.sqrt (2 * B' * (1 + Ξ) / (γ ^ 2 * (1 - γ) ^ 2)) ≤
      Real.sqrt (2 * B' * (1 + Ξ') / (γ ^ 2 * (1 - γ) ^ 2)) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * a1)
  linarith

/-- The deterministic gap bound. -/
theorem gap_le (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    (hatt : ∀ p, RowAttains (ball p σ)) (hself : ∀ p, p ∈ ball p σ) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (T : ℕ) (fh : State → Action)
    (hgreedy : IsGreedy (empiricalDRVI ball M σ N hN data T) fh)
    {B' Ξ a1 a0 : ℝ} (hγpos : 0 < M.discount) (ha1 : 0 ≤ a1) (ha0 : 0 ≤ a0)
    (hΞ : 2 * (M.discount ^ T / (1 - M.discount)) ≤ Ξ)
    (hspanA : ∀ x y, empVal ball M N hN σ false (optPolicy (ballFamily ball M σ) M) data x -
      empVal ball M N hN σ false (optPolicy (ballFamily ball M σ) M) data y ≤ B')
    (hspanB : ∀ x y, empVal ball M N hN σ true (optPolicy (ballFamily ball M σ) M) data x -
      empVal ball M N hN σ true (optPolicy (ballFamily ball M σ) M) data y ≤ B')
    (hdev : ∀ (b : Bool) (t : State) (a : Action), ∀ q ∈ ball (M.transition t a) σ,
      |rowInf (ball (empiricalRow N hN data t a) σ)
          (empVal ball M N hN σ b (optPolicy (ballFamily ball M σ) M) data) -
        rowInf (ball (M.transition t a) σ)
          (empVal ball M N hN σ b (optPolicy (ballFamily ball M σ) M) data)| ≤
        a1 * Real.sqrt (q.variance (empVal ball M N hN σ b (optPolicy (ballFamily ball M σ) M) data))
          + a0)
    (s : State) :
    robustOptimalValue ball M σ s - robustPolicyValue ball M σ (detPolicy fh) s ≤
      2 * selfBoundExpr M.discount B' Ξ a1 a0 + Ξ / (1 - M.discount) := by
  haveI := M.state_nonempty
  set U := ballFamily ball M σ with hUdef
  set Mh := empiricalModel M N hN data
  set Uh := empFam ball M N hN σ data
  set πs := optPolicy U M
  have hU : ∀ s a, RowAttains (U s a) := fun s a ↦ hatt _
  have hUne : ∀ s a, (U s a).Nonempty := fun s a ↦ ⟨_, hself _⟩
  have hUhne : ∀ s a, (Uh s a).Nonempty := fun s a ↦ ⟨_, hself _⟩
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hpos : 0 < 1 - M.discount := by linarith
  have hr : Mh.reward = M.reward := rfl
  have hγ : Mh.discount = M.discount := rfl
  set YA := policyFix Uh Mh (detPolicy πs)
  set YB := optFix Uh Mh
  have hYAeq : YA = empVal ball M N hN σ false πs data := rfl
  have hYBeq : YB = empVal ball M N hN σ true πs data := rfl
  set ZA := policyFix U M (detPolicy πs)
  set ZB := policyFix U M (detPolicy fh)
  have hVstar : robustOptimalValue ball M σ s = ZA s := by
    rw [robustOptimalValue_eq_optFix ball M σ hU, ← policyFix_optPolicy]
  have hVπ : robustPolicyValue ball M σ (detPolicy fh) s = ZB s := by
    rw [robustPolicyValue_eq_policyFix ball M σ hU]
  rw [hVstar, hVπ]
  -- residual ξ of the greedy selector
  set ξ : State → ℝ := fun t ↦ YB t - robustQ Uh Mh YB t (fh t)
  have hξb : ∀ t, 0 ≤ ξ t ∧ ξ t ≤ 2 * (M.discount ^ T / (1 - M.discount)) := by
    intro t
    have := greedy_residual_bounds ball Mh σ (fun s a ↦ ⟨_, hself _⟩) T hgreedy t
    exact this
  have hξΞ : ∀ t, ξ t ≤ Ξ := fun t ↦ (hξb t).2.trans hΞ
  have hYB : ∀ t, YB t = robustQ Uh Mh YB t (fh t) + ξ t := fun t ↦ by simp only [ξ]; ring
  have hYA : ∀ t, YA t = robustQ Uh Mh YA t (πs t) + (fun _ ↦ (0 : ℝ)) t := by
    intro t
    have := congrFun (policyFix_spec Uh Mh (detPolicy πs)) t
    rw [policyOp_detPolicy] at this
    simp only [add_zero]
    exact this.symm
  -- deviation vectors
  set dA : State → ℝ := fun t ↦ rowInf (Uh t (πs t)) YA - rowInf (U t (πs t)) YA
  set dB : State → ℝ := fun t ↦ rowInf (Uh t (fh t)) YB - rowInf (U t (fh t)) YB
  set KA := worstKernel U hU YA
  set KB := worstKernel U hU ZB
  have hYA0 : ∀ x, 0 ≤ YA x := fun x ↦ (policyFix_bounds Uh hUhne Mh _ x).1
  have hYB0 : ∀ x, 0 ≤ YB x := fun x ↦ (optFix_bounds Uh hUhne Mh x).1
  -- self-bounds
  have hXA := selfBound M KA πs YA dA (fun _ ↦ 0) (Ξ := 0) hγpos hYA0
    (fun x y ↦ by rw [hYAeq]; exact hspanA x y)
    (fun t ↦ residual_le U Uh M Mh hr hγ πs KA (worstKernel_mem U hU YA) YA _ hYA t)
    (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) ha1 ha0
    (fun t ↦ by
      have := hdev false t (πs t) (KA t (πs t)) (worstKernel_mem U hU YA t (πs t))
      rw [← hYAeq] at this
      exact this)
  have hXB := selfBound M KB fh YB dB ξ (Ξ := Ξ) hγpos hYB0
    (fun x y ↦ by rw [hYBeq]; exact hspanB x y)
    (fun t ↦ residual_le U Uh M Mh hr hγ fh KB (worstKernel_mem U hU ZB) YB ξ hYB t)
    (fun t ↦ (hξb t).1) hξΞ ha1 ha0
    (fun t ↦ by
      have := hdev true t (fh t) (KB t (fh t)) (worstKernel_mem U hU ZB t (fh t))
      rw [← hYBeq] at this
      exact this)
  have hB' : 0 ≤ B' := by have := hspanA s s; linarith
  have hXA' := hXA.trans (selfBoundExpr_mono_Ξ (γ := M.discount) (a0 := a0) hB' ha1
    (show (0 : ℝ) ≤ Ξ from (hξb s).1.trans (hξΞ s)))
  -- the three pieces
  have hA := caseA_le U Uh hU M Mh hr hγ πs s
  have hB := caseB_le U Uh hU M Mh hr hγ fh YB ξ hYB s
  have hmid : YA s ≤ YB s := policyFix_le_optFix Uh Mh _ s
  have hRA : (kernelResolvent M KA πs *ᵥ (fun t ↦ |dA t|)) s ≤
      selfBoundExpr M.discount B' Ξ a1 a0 := (le_norm_self s).trans hXA'
  have hRB : (kernelResolvent M KB fh *ᵥ (fun t ↦ |dB t|)) s ≤
      selfBoundExpr M.discount B' Ξ a1 a0 := (le_norm_self s).trans hXB
  have hRξ : (kernelResolvent M KB fh *ᵥ ξ) s ≤ Ξ / (1 - M.discount) := by
    have := kernelResolvent_mono M KB fh (u := ξ) (v := fun _ ↦ Ξ) hξΞ s
    rwa [kernelResolvent_const] at this
  have hRA0 : 0 ≤ (kernelResolvent M KA πs *ᵥ (fun t ↦ |dA t|)) s :=
    kernelResolvent_nonneg M KA πs (fun _ ↦ abs_nonneg _) s
  have hRB0 : 0 ≤ (kernelResolvent M KB fh *ᵥ (fun t ↦ |dB t|)) s :=
    kernelResolvent_nonneg M KB fh (fun _ ↦ abs_nonneg _) s
  have h1 : M.discount * (kernelResolvent M KA πs *ᵥ (fun t ↦ |dA t|)) s ≤
      selfBoundExpr M.discount B' Ξ a1 a0 := by nlinarith
  have h2 : M.discount * (kernelResolvent M KB fh *ᵥ (fun t ↦ |dB t|)) s ≤
      selfBoundExpr M.discount B' Ξ a1 a0 := by nlinarith
  linarith

end StatisticalRL.RobustRL.DRVI

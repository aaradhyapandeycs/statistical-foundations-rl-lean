import Formalization.RobustRL.DRVI.Thm72Main

/-!
# Oracle planners for the TV DRVI bound (Remark 7.1, `remark:tv-upper`)

Source: arXiv:2610.41903v1, `chapters/robust_RL.tex:361–372`. Theorem 7.2's guarantee holds for
any planner on the empirical RMDP whose deterministic output `f` has empirical robust value gap
`V̂^{⋆,σ} − V̂^{f,σ} ≤ Ξ`. The deterministic gap bound `gap_le` used greediness only through the
planning residual `ξ(t) = V̂⋆(t) − Q̂⋆(t, f t)`; this module bounds that residual by the value gap
and re-runs the gap bound with a general residual bound.

Technical debt: `gap_le_of_residual` and `tv_good_gap_of_valueGap` here, and
`tv_selfBoundExpr_le_of_planning` in `OraclePlannerNumerics`, are textual copies of `gap_le`,
`tv_good_gap` and `tv_selfBoundExpr_le` with only the residual/planning hypotheses generalized. The
originals are special cases and could later be derived from the copies; this was deliberately not
done here so that the corrected Theorem 7.2 proof is unchanged.
-/

open scoped BigOperators Matrix
open MeasureTheory

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7
open StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The planning residual of a deterministic policy is nonnegative and at most its value gap:
`0 ≤ V⋆(t) − Q⋆(t, f t) ≤ V⋆(t) − V^f(t)` for robust fixed points of a row family with nonempty
rows. -/
theorem residual_le_valueGap (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (hU : ∀ s a, (U s a).Nonempty) (f : State → Action) (t : State) :
    0 ≤ optFix U M t - robustQ U M (optFix U M) t (f t) ∧
      optFix U M t - robustQ U M (optFix U M) t (f t) ≤
        optFix U M t - policyFix U M (detPolicy f) t := by
  refine ⟨sub_nonneg.mpr (optQ_le_optFix U M t (f t)), ?_⟩
  have hle : ∀ x, policyFix U M (detPolicy f) x ≤ optFix U M x :=
    policyFix_le_optFix U M (detPolicy f)
  have hZ : policyFix U M (detPolicy f) t =
      robustQ U M (policyFix U M (detPolicy f)) t (f t) := by
    have := congrFun (policyFix_spec U M (detPolicy f)) t
    rw [policyOp_detPolicy] at this
    exact this.symm
  have hmono : robustQ U M (policyFix U M (detPolicy f)) t (f t) ≤
      robustQ U M (optFix U M) t (f t) := by
    unfold robustQ
    exact add_le_add_right (mul_le_mul_of_nonneg_left (rowInf_mono (hU t (f t)) hle)
      M.discount_nonneg) _
  linarith

/-- The deterministic gap bound for an arbitrary deterministic planner output `fh`: a copy of
`gap_le` in which greediness for the DRVI iterate (used there only through the residual bounds
`greedy_residual_bounds`) is replaced by a direct bound `0 ≤ ξ ≤ Ξ` on the empirical planning
residual `ξ(t) = V̂⋆(t) − Q̂⋆(t, fh t)`. -/
theorem gap_le_of_residual (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    (hatt : ∀ p, RowAttains (ball p σ)) (hself : ∀ p, p ∈ ball p σ) (N : ℕ) (hN : 0 < N)
    (data : Samples State Action N) (fh : State → Action)
    {B' Ξ a1 a0 : ℝ} (hγpos : 0 < M.discount) (ha1 : 0 ≤ a1) (ha0 : 0 ≤ a0)
    (hres : ∀ t, 0 ≤ optFix (empFam ball M N hN σ data) (empiricalModel M N hN data) t -
        robustQ (empFam ball M N hN σ data) (empiricalModel M N hN data)
          (optFix (empFam ball M N hN σ data) (empiricalModel M N hN data)) t (fh t) ∧
      optFix (empFam ball M N hN σ data) (empiricalModel M N hN data) t -
        robustQ (empFam ball M N hN σ data) (empiricalModel M N hN data)
          (optFix (empFam ball M N hN σ data) (empiricalModel M N hN data)) t (fh t) ≤ Ξ)
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
  have hξb : ∀ t, 0 ≤ ξ t ∧ ξ t ≤ Ξ := hres
  have hξΞ : ∀ t, ξ t ≤ Ξ := fun t ↦ (hξb t).2
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

/-- Deterministic TV gap bound on the good event for an arbitrary deterministic planner output
`fh` whose empirical robust value gap is at most `Ξ` (copy of `tv_good_gap` with the DRVI
greediness replaced by the value-gap requirement). -/
theorem tv_good_gap_of_valueGap (M : DiscountedMDP State Action) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hγpos : 0 < M.discount) (N : ℕ) (hN : 0 < N) (data : Samples State Action N) {ℓ : ℝ}
    (hℓ0 : 0 ≤ ℓ)
    (hgood : ∀ (x : State) (a : Action) (k : Bool × Fin (N + 1) × Fin (N + 1)),
      |(empiricalRow N hN data x a).expectation
          (clipFamily tvBall M N hN σ (optPolicy (ballFamily tvBall M σ) M) x k
            (offStateData x N data)) -
        (M.transition x a).expectation
          (clipFamily tvBall M N hN σ (optPolicy (ballFamily tvBall M σ) M) x k
            (offStateData x N data))| ≤
        Real.sqrt (2 * ℓ * (M.transition x a).variance
          (clipFamily tvBall M N hN σ (optPolicy (ballFamily tvBall M σ) M) x k
            (offStateData x N data)) / N) +
          2 * (1 / (1 - M.discount)) * ℓ / (3 * N))
    (fh : State → Action) {Ξ : ℝ}
    (hgap : ∀ t, robustOptimalValue tvBall (empiricalModel M N hN data) σ t -
      robustPolicyValue tvBall (empiricalModel M N hN data) σ (detPolicy fh) t ≤ Ξ)
    (s : State) :
    robustOptimalValue tvBall M σ s - robustPolicyValue tvBall M σ (detPolicy fh) s ≤
      2 * selfBoundExpr M.discount (1 / (1 - M.discount + M.discount * σ))
          Ξ (Real.sqrt (2 * ℓ / N))
          (Real.sqrt (2 * ℓ / N) * (1 / (N * (1 - M.discount)) +
              Real.sqrt (σ * (1 / (1 - M.discount + M.discount * σ)) ^ 2)) +
            2 * (1 / (1 - M.discount)) * ℓ / (3 * N) + 4 * (1 / (N * (1 - M.discount)))) +
        Ξ / (1 - M.discount) := by
  haveI := M.state_nonempty
  have hσ0' : 0 ≤ σ := hσ0.le
  have hself : ∀ p : FiniteDistribution State, p ∈ tvBall p σ := fun p ↦ tvBall_self_mem p hσ0'
  have hatt : ∀ p : FiniteDistribution State, RowAttains (tvBall p σ) :=
    fun p ↦ tvBall_rowAttains p hσ0'
  have hpos : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set πs := optPolicy (ballFamily tvBall M σ) M
  set B' := 1 / (1 - M.discount + M.discount * σ)
  set step := gridStep M N with hstepdef
  have hstep : 0 < step := gridStep_pos M hN
  have hNstep : (N : ℝ) * step = 1 / (1 - M.discount) := N_mul_gridStep M hN
  have hstepeq : step = 1 / (N * (1 - M.discount)) := rfl
  set a1 := Real.sqrt (2 * ℓ / N)
  have ha1 : 0 ≤ a1 := Real.sqrt_nonneg _
  have hspan : ∀ (b : Bool) x y, empVal tvBall M N hN σ b πs data x -
      empVal tvBall M N hN σ b πs data y ≤ B' := by
    intro b x y
    unfold empVal empFam
    cases b
    · exact tv_policyFix_span (empiricalModel M N hN data) hσ0' hσ1 _ x y
    · exact tv_optFix_span (empiricalModel M N hN data) hσ0' hσ1 x y
  rw [← hstepeq]
  have hres : ∀ t, 0 ≤ optFix (empFam tvBall M N hN σ data) (empiricalModel M N hN data) t -
        robustQ (empFam tvBall M N hN σ data) (empiricalModel M N hN data)
          (optFix (empFam tvBall M N hN σ data) (empiricalModel M N hN data)) t (fh t) ∧
      optFix (empFam tvBall M N hN σ data) (empiricalModel M N hN data) t -
        robustQ (empFam tvBall M N hN σ data) (empiricalModel M N hN data)
          (optFix (empFam tvBall M N hN σ data) (empiricalModel M N hN data)) t (fh t) ≤ Ξ := by
    intro t
    have hr := residual_le_valueGap (empFam tvBall M N hN σ data) (empiricalModel M N hN data)
      (fun s a ↦ ⟨_, hself _⟩) fh t
    have hg := hgap t
    rw [robustOptimalValue_eq_optFix tvBall _ σ (tvBall_family_rowAttains _ hσ0'),
      robustPolicyValue_eq_policyFix tvBall _ σ (tvBall_family_rowAttains _ hσ0')] at hg
    exact ⟨hr.1, hr.2.trans hg⟩
  apply gap_le_of_residual tvBall M σ hatt hself N hN data fh hγpos ha1 (by positivity) hres
    (hspan false) (hspan true)
  intro b t a q hq
  obtain ⟨i, hi, hclose⟩ := exists_grid_close tvBall M N hN σ hself b πs t data
  set Y := empVal tvBall M N hN σ b πs data
  set W := absVal tvBall M N hN σ b πs t (i * step) data
  have hW0 : ∀ y, 0 ≤ W y := fun y ↦ (absVal_bounds tvBall M N hN σ hself b πs t _ data y).1
  have hWB : ∀ y, W y ≤ N * step := fun y ↦ by
    rw [hNstep]; exact (absVal_bounds tvBall M N hN σ hself b πs t _ data y).2
  have hbern : ∀ j : ℕ, j ≤ N →
      |(empiricalRow N hN data t a).expectation (fun x ↦ min (W x) (j * step)) -
        (M.transition t a).expectation (fun x ↦ min (W x) (j * step))| ≤
      Real.sqrt (2 * ℓ * (M.transition t a).variance (fun x ↦ min (W x) (j * step)) / N) +
        2 * (1 / (1 - M.discount)) * ℓ / (3 * N) := by
    intro j hj
    have h := hgood t a (b, ⟨i, Nat.lt_succ_of_le hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩)
    rw [clipFamily_offState] at h
    exact h
  have hdevY := tv_row_deviation (M.transition t a) (empiricalRow N hN data t a) hσ0 hstep hN hℓ0
    hW0 hWB hNstep hclose hbern
  have htransfer := std_le_of_variance_le (by positivity)
    (tv_variance_transfer hq (hspan b))
  calc _ ≤ a1 * (Real.sqrt ((M.transition t a).variance Y) + step) +
        2 * (1 / (1 - M.discount)) * ℓ / (3 * N) + 4 * step := hdevY
    _ ≤ a1 * ((Real.sqrt (q.variance Y) + Real.sqrt (σ * B' ^ 2)) + step) +
        2 * (1 / (1 - M.discount)) * ℓ / (3 * N) + 4 * step := by
        have := mul_le_mul_of_nonneg_left (add_le_add_right htransfer step) ha1
        linarith
    _ = a1 * Real.sqrt (q.variance Y) + (a1 * (step + Real.sqrt (σ * B' ^ 2)) +
        2 * (1 / (1 - M.discount)) * ℓ / (3 * N) + 4 * step) := by ring

end StatisticalRL.RobustRL.DRVI

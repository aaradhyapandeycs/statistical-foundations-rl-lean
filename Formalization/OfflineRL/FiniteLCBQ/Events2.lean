import Formalization.OfflineRL.FiniteLCBQ.Events

/-!
# Finite-horizon LCB-Q: the change-of-measure events M1, M2 and the count event Cnt
-/

namespace StatisticalRL.LCBQFinite

open Finset MeasureTheory ProbabilityTheory OnlineRL StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance ev2DecS : DecidableEq S := Classical.decEq S
noncomputable local instance ev2DecA : DecidableEq A := Classical.decEq A

variable {H K : ℕ} (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
  (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A) (cb L : ℝ) (sel : (A → ℝ) → A)
  (π₀ : Fin H → S → A)

/-- One-step expectation of a function of `(s_h, a_h)`. -/
theorem pair_sum (h : Fin H) (ψ : S → A → ℝ) :
    ∑ τ, trajProb E πb ρb τ * ψ (τ.1 h.castSucc) (τ.2 h) =
      ∑ s, ∑ a, occupancy E πb ρb h s a * ψ s a := by
  have := sum_traj_triple E πb ρb h (fun s0 a0 _ ↦ ψ s0 a0)
  simp only [← sum_mul, FiniteDistribution.sum_prob, one_mul] at this
  exact this

/-- `Σ_{s,a} d^b_h(s,a) 1{a = π⋆_h(s)} u(s) = Σ_s d^b_h(s,π⋆_h(s)) u(s)`. -/
theorem occ_sel_sum (h : Fin H) (u : S → ℝ) :
    ∑ s, ∑ a, occupancy E πb ρb h s a * (if a = πs h s then u s else 0) =
      ∑ s, db E πb ρb πs h s * u s := by
  refine sum_congr rfl fun s _ ↦ ?_
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true, db]

/-! ## Predictable functions -/

/-- `f(s) = min((Q⋆_h - Q_h)^+(s,π⋆_h(s)), H)` for an iterate. -/
noncomputable def fIt (it : Iterate S A H) (h : Fin H) (s : S) : ℝ :=
  min (max (Qs E h s (πs h s) - it.Q h s (πs h s)) 0) H

/-- `g(s) = P_h(s,π⋆_h(s))·(V⋆_{h+1} - V_{h+1})^+` for an iterate. -/
noncomputable def gIt (it : Iterate S A H) (h : Fin H) (s : S) : ℝ :=
  ((E h).transition s (πs h s)).expectation (fun t ↦ max (optV E (h.val + 1) t - nextV it h t) 0)

theorem fK_eq (x : Fin K → Traj S A H) (k : ℕ) (h : Fin H) (s : S) :
    fK E πs cb L sel π₀ x k h s = fIt E πs (it E cb L sel π₀ x k) h s := rfl

theorem gK_eq (x : Fin K → Traj S A H) (k : ℕ) (h : Fin H) (s : S) :
    gK E πs cb L sel π₀ x k h s = gIt E πs (it E cb L sel π₀ x k) h s := rfl

/-- `Z = w(s_h) 1{a_h = π⋆_h(s_h)} u(s_h)` evaluated at `(s0,a0)`. -/
noncomputable def zOf (h : Fin H) (u : S → ℝ) (s0 : S) (a0 : A) : ℝ :=
  if a0 = πs h s0 then wt E πb ρb ρ πs h s0 * u s0 else 0

theorem sum_vis_eq_zOf (x : Fin K → Traj S A H) (h : Fin H) (u : S → ℝ) (k : Fin K) :
    (∑ s, if visA πs x h s k.val then wt E πb ρb ρ πs h s * u s else 0) =
      zOf E πb ρb ρ πs h u ((x k).1 h.castSucc) ((x k).2 h) := by
  unfold zOf
  rw [sum_eq_single ((x k).1 h.castSucc)]
  · by_cases ha : (x k).2 h = πs h ((x k).1 h.castSucc)
    · rw [if_pos ((vis_fin_iff x h _ _ k).2 ⟨rfl, ha⟩), if_pos ha]
    · rw [if_neg (fun hv ↦ ha ((vis_fin_iff x h _ _ k).1 hv).2), if_neg ha]
  · intro s _ hs
    rw [if_neg (fun hv ↦ hs ((vis_fin_iff x h _ _ k).1 hv).1.symm)]
  · simp

section Moments

variable (hC : concentrability E πb ρb ρ πs ≠ ⊤)
include hC

/-- First moment: `E Z = Σ_s d⋆_h(s) u(s)`. -/
theorem zOf_mean (h : Fin H) (u : S → ℝ) :
    ∑ s, ∑ a, occupancy E πb ρb h s a * zOf E πb ρb ρ πs h u s a = ∑ s, ds E ρ πs h s * u s := by
  unfold zOf
  rw [occ_sel_sum]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [← mul_assoc, mul_comm (db E πb ρb πs h s), wt_mul_db E πb ρb ρ πs hC h s]

/-- Second moment: `E Z² ≤ C⋆ H Σ_s d⋆_h(s) u(s)` for `u ∈ [0,H]`. -/
theorem zOf_second (h : Fin H) (u : S → ℝ) (hu : ∀ s, 0 ≤ u s ∧ u s ≤ H) :
    ∑ s, ∑ a, occupancy E πb ρb h s a * (zOf E πb ρb ρ πs h u s a) ^ 2 ≤
      (concentrability E πb ρb ρ πs).toReal * H * ∑ s, ds E ρ πs h s * u s := by
  have e : ∀ s a, (zOf E πb ρb ρ πs h u s a) ^ 2 =
      if a = πs h s then (wt E πb ρb ρ πs h s * u s) ^ 2 else 0 := by
    intro s a; unfold zOf; split_ifs <;> ring
  simp only [e]
  rw [occ_sel_sum, mul_sum]
  refine sum_le_sum fun s _ ↦ ?_
  have hw0 := wt_nonneg E πb ρb ρ πs hC h s
  have hwC := wt_le E πb ρb ρ πs hC h s
  have hd0 := ds_nonneg E ρ πs h s
  have h1 : db E πb ρb πs h s * (wt E πb ρb ρ πs h s * u s) ^ 2 =
      ds E ρ πs h s * (wt E πb ρb ρ πs h s * (u s * u s)) := by
    rw [← wt_mul_db E πb ρb ρ πs hC h s]; ring
  rw [h1]
  have h2 : wt E πb ρb ρ πs h s * (u s * u s) ≤ (concentrability E πb ρb ρ πs).toReal * (H * u s) :=
    mul_le_mul hwC (mul_le_mul_of_nonneg_right (hu s).2 (hu s).1) (mul_nonneg (hu s).1 (hu s).1)
      ENNReal.toReal_nonneg
  calc _ ≤ ds E ρ πs h s * ((concentrability E πb ρb ρ πs).toReal * (H * u s)) :=
        mul_le_mul_of_nonneg_left h2 hd0
    _ = _ := by ring

theorem zOf_nonneg (h : Fin H) (u : S → ℝ) (hu : ∀ s, 0 ≤ u s) (s : S) (a : A) :
    0 ≤ zOf E πb ρb ρ πs h u s a := by
  unfold zOf; split_ifs
  · exact mul_nonneg (wt_nonneg E πb ρb ρ πs hC h s) (hu s)
  · exact le_rfl

theorem zOf_le (h : Fin H) (u : S → ℝ) (hu : ∀ s, 0 ≤ u s ∧ u s ≤ H) (s : S) (a : A) :
    zOf E πb ρb ρ πs h u s a ≤ (concentrability E πb ρb ρ πs).toReal * H := by
  unfold zOf; split_ifs
  · exact mul_le_mul (wt_le E πb ρb ρ πs hC h s) (hu s).2 (hu s).1 ENNReal.toReal_nonneg
  · exact mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg H)

/-- One-step bound for the M1 increment `-λZ + λa - λ²C⋆Ha` (`λ C⋆ H ≤ 1`). -/
theorem m1_step (h : Fin H) (u : S → ℝ) (hu : ∀ s, 0 ≤ u s ∧ u s ≤ H) {lam : ℝ} (hl0 : 0 ≤ lam)
    (hl1 : lam * ((concentrability E πb ρb ρ πs).toReal * H) ≤ 1) :
    ∑ s, ∑ a, occupancy E πb ρb h s a * Real.exp (-lam * zOf E πb ρb ρ πs h u s a +
      lam * ∑ t, ds E ρ πs h t * u t -
      lam ^ 2 * ((concentrability E πb ρb ρ πs).toReal * H) * ∑ t, ds E ρ πs h t * u t) ≤ 1 := by
  set C := (concentrability E πb ρb ρ πs).toReal
  set m := ∑ t, ds E ρ πs h t * u t
  set c := lam * m - lam ^ 2 * (C * H) * m
  have hpt : ∀ s a, Real.exp (-lam * zOf E πb ρb ρ πs h u s a) ≤
      1 - lam * zOf E πb ρb ρ πs h u s a + lam ^ 2 * (zOf E πb ρb ρ πs h u s a) ^ 2 := by
    intro s a
    have hz0 := zOf_nonneg E πb ρb ρ πs hC h u (fun s ↦ (hu s).1) s a
    have hz1 := zOf_le E πb ρb ρ πs hC h u hu s a
    have habs : |(-lam * zOf E πb ρb ρ πs h u s a)| ≤ 1 := by
      rw [abs_le]; constructor
      · nlinarith [mul_le_mul_of_nonneg_left hz1 hl0]
      · nlinarith [mul_nonneg hl0 hz0]
    have := exp_le_quad habs
    nlinarith [this]
  have hsum : ∑ s, ∑ a, occupancy E πb ρb h s a * Real.exp (-lam * zOf E πb ρb ρ πs h u s a) ≤
      1 - lam * m + lam ^ 2 * (C * H * m) := by
    calc _ ≤ ∑ s, ∑ a, occupancy E πb ρb h s a * (1 - lam * zOf E πb ρb ρ πs h u s a +
          lam ^ 2 * (zOf E πb ρb ρ πs h u s a) ^ 2) :=
          sum_le_sum fun s _ ↦ sum_le_sum fun a _ ↦
            mul_le_mul_of_nonneg_left (hpt s a) (occupancy_nonneg E πb ρb h s a)
      _ = (∑ s, ∑ a, occupancy E πb ρb h s a) -
          lam * (∑ s, ∑ a, occupancy E πb ρb h s a * zOf E πb ρb ρ πs h u s a) +
          lam ^ 2 * (∑ s, ∑ a, occupancy E πb ρb h s a * (zOf E πb ρb ρ πs h u s a) ^ 2) := by
          simp only [mul_add, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, mul_sum]
          refine congrArg₂ _ (congrArg₂ _ rfl (sum_congr rfl fun s _ ↦ sum_congr rfl
            fun a _ ↦ by ring)) (sum_congr rfl fun s _ ↦ sum_congr rfl fun a _ ↦ by ring)
      _ ≤ 1 - lam * m + lam ^ 2 * (C * H * m) := by
          rw [sum_occupancy, zOf_mean E πb ρb ρ πs hC]
          have := zOf_second E πb ρb ρ πs hC h u hu
          have := mul_le_mul_of_nonneg_left this (sq_nonneg lam)
          simp only [m, C] at *
          linarith
  have hfac : ∀ s a, Real.exp (-lam * zOf E πb ρb ρ πs h u s a + lam * m - lam ^ 2 * (C * H) * m) =
      Real.exp c * Real.exp (-lam * zOf E πb ρb ρ πs h u s a) := by
    intro s a; rw [← Real.exp_add]; congr 1; simp only [c]; ring
  simp only [hfac]
  have e2 : ∑ s, ∑ a, occupancy E πb ρb h s a * (Real.exp c *
      Real.exp (-lam * zOf E πb ρb ρ πs h u s a)) = Real.exp c *
      ∑ s, ∑ a, occupancy E πb ρb h s a * Real.exp (-lam * zOf E πb ρb ρ πs h u s a) := by
    rw [mul_sum]; refine sum_congr rfl fun s _ ↦ ?_; rw [mul_sum]
    refine sum_congr rfl fun a _ ↦ by ring
  rw [e2]
  calc _ ≤ Real.exp c * (1 - lam * m + lam ^ 2 * (C * H * m)) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ ≤ Real.exp c * Real.exp (-c) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have := Real.add_one_le_exp (-c)
        simp only [c] at this ⊢; linarith
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- One-step bound for the M2 increment `λZ - λa - λ²C⋆Ha` (`λ C⋆ H ≤ 1`). -/
theorem m2_step (h : Fin H) (u : S → ℝ) (hu : ∀ s, 0 ≤ u s ∧ u s ≤ H) {lam : ℝ} (hl0 : 0 ≤ lam)
    (hl1 : lam * ((concentrability E πb ρb ρ πs).toReal * H) ≤ 1) :
    ∑ s, ∑ a, occupancy E πb ρb h s a * Real.exp (lam * zOf E πb ρb ρ πs h u s a -
      lam * ∑ t, ds E ρ πs h t * u t -
      lam ^ 2 * ((concentrability E πb ρb ρ πs).toReal * H) * ∑ t, ds E ρ πs h t * u t) ≤ 1 := by
  set C := (concentrability E πb ρb ρ πs).toReal
  set m := ∑ t, ds E ρ πs h t * u t
  set c := lam * m + lam ^ 2 * (C * H) * m
  have hpt : ∀ s a, Real.exp (lam * zOf E πb ρb ρ πs h u s a) ≤
      1 + lam * zOf E πb ρb ρ πs h u s a + lam ^ 2 * (zOf E πb ρb ρ πs h u s a) ^ 2 := by
    intro s a
    have hz0 := zOf_nonneg E πb ρb ρ πs hC h u (fun s ↦ (hu s).1) s a
    have hz1 := zOf_le E πb ρb ρ πs hC h u hu s a
    have habs : |lam * zOf E πb ρb ρ πs h u s a| ≤ 1 := by
      rw [abs_le]; constructor
      · nlinarith [mul_nonneg hl0 hz0]
      · nlinarith [mul_le_mul_of_nonneg_left hz1 hl0]
    have := exp_le_quad habs
    nlinarith [this]
  have hsum : ∑ s, ∑ a, occupancy E πb ρb h s a * Real.exp (lam * zOf E πb ρb ρ πs h u s a) ≤
      1 + lam * m + lam ^ 2 * (C * H * m) := by
    calc _ ≤ ∑ s, ∑ a, occupancy E πb ρb h s a * (1 + lam * zOf E πb ρb ρ πs h u s a +
          lam ^ 2 * (zOf E πb ρb ρ πs h u s a) ^ 2) :=
          sum_le_sum fun s _ ↦ sum_le_sum fun a _ ↦
            mul_le_mul_of_nonneg_left (hpt s a) (occupancy_nonneg E πb ρb h s a)
      _ = (∑ s, ∑ a, occupancy E πb ρb h s a) +
          lam * (∑ s, ∑ a, occupancy E πb ρb h s a * zOf E πb ρb ρ πs h u s a) +
          lam ^ 2 * (∑ s, ∑ a, occupancy E πb ρb h s a * (zOf E πb ρb ρ πs h u s a) ^ 2) := by
          simp only [mul_add, mul_one, sum_add_distrib, mul_sum]
          refine congrArg₂ _ (congrArg₂ _ rfl (sum_congr rfl fun s _ ↦ sum_congr rfl
            fun a _ ↦ by ring)) (sum_congr rfl fun s _ ↦ sum_congr rfl fun a _ ↦ by ring)
      _ ≤ 1 + lam * m + lam ^ 2 * (C * H * m) := by
          rw [sum_occupancy, zOf_mean E πb ρb ρ πs hC]
          have := zOf_second E πb ρb ρ πs hC h u hu
          have := mul_le_mul_of_nonneg_left this (sq_nonneg lam)
          simp only [m, C] at *
          linarith
  have hfac : ∀ s a, Real.exp (lam * zOf E πb ρb ρ πs h u s a - lam * m - lam ^ 2 * (C * H) * m) =
      Real.exp (-c) * Real.exp (lam * zOf E πb ρb ρ πs h u s a) := by
    intro s a; rw [← Real.exp_add]; congr 1; simp only [c]; ring
  simp only [hfac]
  have e2 : ∑ s, ∑ a, occupancy E πb ρb h s a * (Real.exp (-c) *
      Real.exp (lam * zOf E πb ρb ρ πs h u s a)) = Real.exp (-c) *
      ∑ s, ∑ a, occupancy E πb ρb h s a * Real.exp (lam * zOf E πb ρb ρ πs h u s a) := by
    rw [mul_sum]; refine sum_congr rfl fun s _ ↦ ?_; rw [mul_sum]
    refine sum_congr rfl fun a _ ↦ by ring
  rw [e2]
  calc _ ≤ Real.exp (-c) * (1 + lam * m + lam ^ 2 * (C * H * m)) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ ≤ Real.exp (-c) * Real.exp c := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have := Real.add_one_le_exp c
        simp only [c] at this ⊢; linarith
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end Moments

/-! ## Count event -/

theorem cnt_step (h : Fin H) (s : S) :
    ∑ s0, ∑ a0, occupancy E πb ρb h s0 a0 *
      Real.exp ((if s0 = s ∧ a0 = πs h s then 1 else 0) - 2 * db E πb ρb πs h s) ≤ 1 := by
  set d := db E πb ρb πs h s
  have hd0 : 0 ≤ d := db_nonneg E πb ρb πs h s
  have e : ∀ s0 a0, occupancy E πb ρb h s0 a0 *
      Real.exp ((if s0 = s ∧ a0 = πs h s then 1 else 0) - 2 * d) =
      Real.exp (-(2 * d)) * (occupancy E πb ρb h s0 a0 +
        (if s0 = s ∧ a0 = πs h s then (Real.exp 1 - 1) * d else 0)) := by
    intro s0 a0
    by_cases hc : s0 = s ∧ a0 = πs h s
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [and_self, if_true]
      rw [show (1 : ℝ) - 2 * d = 1 + -(2 * d) by ring, Real.exp_add]
      simp only [d, db]; ring
    · simp only [hc, if_false, zero_sub, add_zero]; ring
  simp only [e]
  have e2 : ∑ x : S, ∑ a : A, Real.exp (-(2 * d)) * (occupancy E πb ρb h x a +
      (if x = s ∧ a = πs h s then (Real.exp 1 - 1) * d else 0)) =
      Real.exp (-(2 * d)) * ((∑ x : S, ∑ a : A, occupancy E πb ρb h x a) +
        ∑ x : S, ∑ a : A, (if x = s ∧ a = πs h s then (Real.exp 1 - 1) * d else 0)) := by
    rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun a _ ↦ by ring
  rw [e2, sum_occupancy]
  have hs : ∑ x : S, ∑ a : A, (if x = s ∧ a = πs h s then (Real.exp 1 - 1) * d else 0) =
      (Real.exp 1 - 1) * d := by
    rw [sum_eq_single s]
    · rw [sum_eq_single (πs h s)]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [hs]
  have he : Real.exp 1 - 1 ≤ 2 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  calc Real.exp (-(2 * d)) * (1 + (Real.exp 1 - 1) * d) ≤ Real.exp (-(2 * d)) * (1 + 2 * d) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        nlinarith
    _ ≤ Real.exp (-(2 * d)) * Real.exp (2 * d) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have := Real.add_one_le_exp (2 * d); linarith
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end StatisticalRL.LCBQFinite

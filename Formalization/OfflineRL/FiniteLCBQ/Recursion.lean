import Formalization.OfflineRL.FiniteLCBQ.Pessimism
import Formalization.OfflineRL.FiniteVILCB.Links
import Formalization.OfflineRL.VILCBBonusSumScalar
import Formalization.OfflineRL.LCBQUsefulSeries

/-!
# Finite-horizon LCB-Q: the deterministic recursion on the good event (Step 4 of the plan)

On the event `GoodEv` (both sides of E1, the change-of-measure events M1/M2 per stage, and the
count event Cnt per `(h,s)`), the gap sums `G_h = Σ_{k<K} ⟨d⋆_h, (V⋆_h - V^k_h)^+⟩` obey
`G_h ≤ (1+1/H)³ G_{h+1} + R`, hence `G_0 ≤ 21 H R`, and by pessimism the gap of the output policy
is at most `G_0 / K`.
-/

namespace StatisticalRL.LCBQFinite

open Finset OnlineRL StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance rcDecS : DecidableEq S := Classical.decEq S
noncomputable local instance rcDecA : DecidableEq A := Classical.decEq A

variable {H K : ℕ}

/-- `0 ≤ V⋆_h ≤ H - h`. -/
theorem optV_le (E : Fin H → EnvironmentStage S A) :
    ∀ m h, H - h = m → ∀ s, optV E h s ≤ m := by
  intro m
  induction m with
  | zero => intro h hh s; rw [optV_of_ge E (by omega)]; simp
  | succ m ih =>
    intro h hh s
    have hlt : h < H := by omega
    have := optV_of_lt E ⟨h, hlt⟩ s
    simp only at this
    rw [this]
    refine actionMaximum_le fun a ↦ ?_
    have h1 := (E ⟨h, hlt⟩).reward_le_one s a
    have h2 := FiniteDistribution.expectation_le_const ((E ⟨h, hlt⟩).transition s a)
      (fun t ↦ ih (h + 1) (by omega) t)
    push_cast; linarith

theorem optV_le_H (E : Fin H → EnvironmentStage S A) (h : ℕ) (s : S) : optV E h s ≤ H := by
  have := optV_le E (H - h) h rfl s
  have h1 : ((H - h : ℕ) : ℝ) ≤ H := by exact_mod_cast Nat.sub_le H h
  linarith

theorem sum_dstar (E : Fin H → EnvironmentStage S A) (πs : Fin H → S → A)
    (ρ : FiniteDistribution S) {h : ℕ} (hh : h ≤ H) : ∑ s, dstar E πs ρ h s = 1 := by
  simp only [dstar, dif_pos hh]
  have := sum_stateMarg E (detPolicy πs) ρ ⟨h, Nat.lt_succ_of_le hh⟩ (fun _ ↦ 1)
  simp only [mul_one] at this
  rw [this, sum_trajProb]

theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

variable (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
  (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A) (cb L : ℝ) (sel : (A → ℝ) → A)
  (π₀ : Fin H → S → A) (x : Fin K → Traj S A H)

/-! ## The quantities of Step 4 -/

/-- `Q⋆_h(s,a)`. -/
noncomputable def Qs (h : Fin H) (s : S) (a : A) : ℝ :=
  (E h).reward s a + ((E h).transition s a).expectation (optV E (h.val + 1))

/-- `f^k(s) = min((Q⋆_h - Q^k_h)^+(s,π⋆_h(s)), H)` (predictable, in `[0,H]`). -/
noncomputable def fK (k : ℕ) (h : Fin H) (s : S) : ℝ :=
  min (max (Qs E h s (πs h s) - (it E cb L sel π₀ x k).Q h s (πs h s)) 0) H

/-- `g^k(s) = P_h(s,π⋆_h(s))·(V⋆_{h+1} - V^k_{h+1})^+` (predictable, in `[0,H]`). -/
noncomputable def gK (k : ℕ) (h : Fin H) (s : S) : ℝ :=
  ((E h).transition s (πs h s)).expectation
    (fun t ↦ max (optV E (h.val + 1) t - Vn E cb L sel π₀ x k h t) 0)

/-- `d^b_h(s,π⋆_h(s))`. -/
noncomputable def db (h : Fin H) (s : S) : ℝ := occupancy E πb ρb h s (πs h s)

/-- `d⋆_h(s)`. -/
noncomputable def ds (h : Fin H) (s : S) : ℝ := dstar E πs ρ h.val s

/-- The importance weight `w_h(s) = d⋆_h(s)/d^b_h(s,π⋆_h(s))` (`0` if `d^b = 0`). -/
noncomputable def wt (h : Fin H) (s : S) : ℝ :=
  if db E πb ρb πs h s = 0 then 0 else ds E ρ πs h s / db E πb ρb πs h s

/-- Visits of `(h, s, π⋆_h(s))`. -/
abbrev visA (h : Fin H) (s : S) (k : ℕ) : Prop := vis x h s (πs h s) k

/-- `Z^{(1)}_k = w(s_h^k) 1{a_h^k = π⋆} f^k(s_h^k)`. -/
noncomputable def Z1 (k : ℕ) (h : Fin H) : ℝ :=
  ∑ s, if visA πs x h s k then wt E πb ρb ρ πs h s * fK E πs cb L sel π₀ x k h s else 0

noncomputable def a1 (k : ℕ) (h : Fin H) : ℝ := ∑ s, ds E ρ πs h s * fK E πs cb L sel π₀ x k h s

noncomputable def Z2 (k : ℕ) (h : Fin H) : ℝ :=
  ∑ s, if visA πs x h s k then wt E πb ρb ρ πs h s * gK E πs cb L sel π₀ x k h s else 0

noncomputable def a2 (k : ℕ) (h : Fin H) : ℝ := ∑ s, ds E ρ πs h s * gK E πs cb L sel π₀ x k h s

/-- `V^k_h` extended by `0` at `h ≥ H`. -/
noncomputable def Vh (k h : ℕ) (s : S) : ℝ :=
  if hh : h < H then (it E cb L sel π₀ x k).V ⟨h, hh⟩ s else 0

/-- `G_h = Σ_{k<K} ⟨d⋆_h, (V⋆_h - V^k_h)^+⟩`. -/
noncomputable def Gs (h : ℕ) : ℝ :=
  ∑ k ∈ range K, ∑ s, dstar E πs ρ h s * max (optV E h s - Vh E cb L sel π₀ x k h s) 0

/-- The good event, pathwise. -/
structure GoodEv (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
    (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A) (cb L : ℝ) (sel : (A → ℝ) → A)
    (π₀ : Fin H → S → A) (x : Fin K → Traj S A H) (C ι : ℝ) : Prop where
  up : ∀ (h : Fin H) (s : S) (a : A) (n : ℕ), 1 ≤ n → n ≤ K →
    mart E cb L sel π₀ x h s a n ≤ penalty cb L H n
  low : LowerE1 E cb L sel π₀ x
  m1 : ∀ h : Fin H, (1 - 1 / (2 * (H : ℝ))) * ∑ k ∈ range K, a1 E ρ πs cb L sel π₀ x k h ≤
    ∑ k ∈ range K, Z1 E πb ρb ρ πs cb L sel π₀ x k h + 2 * C * (H : ℝ) ^ 2 * ι
  m2 : ∀ h : Fin H, ∑ k ∈ range K, Z2 E πb ρb ρ πs cb L sel π₀ x k h ≤
    (1 + 1 / (H : ℝ)) * ∑ k ∈ range K, a2 E ρ πs cb L sel π₀ x k h + C * (H : ℝ) ^ 2 * ι
  cntb : ∀ (h : Fin H) (s : S),
    (cnt (visA πs x h s) K : ℝ) ≤ 2 * K * db E πb ρb πs h s + ι

/-! ## Elementary facts -/

theorem Vn_eq_Vh (k : ℕ) (h : Fin H) (t : S) :
    Vn E cb L sel π₀ x k h t = Vh E cb L sel π₀ x k (h.val + 1) t := by
  simp only [Vn, nextV, Vh]
  split_ifs <;> rfl

theorem gK_nonneg (k : ℕ) (h : Fin H) (s : S) : 0 ≤ gK E πs cb L sel π₀ x k h s :=
  FiniteDistribution.expectation_nonneg _ fun _ ↦ le_max_right _ _

theorem fK_nonneg (k : ℕ) (h : Fin H) (s : S) : 0 ≤ fK E πs cb L sel π₀ x k h s :=
  le_min (le_max_right _ _) (Nat.cast_nonneg H)

theorem fK_le_H (k : ℕ) (h : Fin H) (s : S) : fK E πs cb L sel π₀ x k h s ≤ H := min_le_right _ _

theorem gK_le_H (k : ℕ) (h : Fin H) (s : S) : gK E πs cb L sel π₀ x k h s ≤ H := by
  refine FiniteDistribution.expectation_le_const _ fun t ↦ max_le ?_ (Nat.cast_nonneg H)
  have := optV_le_H E (h.val + 1) t
  have := nextV_nonneg cb L sel (rw' E) π₀ x k h t
  simp only [Vn] at *
  linarith

theorem ds_nonneg (h : Fin H) (s : S) : 0 ≤ ds E ρ πs h s := (dstar_flow E πs ρ).nonneg _ _

theorem db_nonneg (h : Fin H) (s : S) : 0 ≤ db E πb ρb πs h s := occupancy_nonneg _ _ _ _ _ _

section Weights

variable (hC : concentrability E πb ρb ρ πs ≠ ⊤)
include hC

theorem ds_le (h : Fin H) (s : S) :
    ds E ρ πs h s ≤ (concentrability E πb ρb ρ πs).toReal * db E πb ρb πs h s :=
  dstar_le E πb ρb ρ πs hC h s

theorem wt_nonneg (h : Fin H) (s : S) : 0 ≤ wt E πb ρb ρ πs h s := by
  unfold wt; split_ifs
  · exact le_rfl
  · exact div_nonneg (ds_nonneg E ρ πs h s) (db_nonneg E πb ρb πs h s)

theorem wt_le (h : Fin H) (s : S) : wt E πb ρb ρ πs h s ≤ (concentrability E πb ρb ρ πs).toReal := by
  unfold wt; split_ifs with h0
  · exact ENNReal.toReal_nonneg
  · rw [div_le_iff₀ (lt_of_le_of_ne (db_nonneg E πb ρb πs h s) (Ne.symm h0))]
    exact ds_le E πb ρb ρ πs hC h s

theorem wt_mul_db (h : Fin H) (s : S) : wt E πb ρb ρ πs h s * db E πb ρb πs h s = ds E ρ πs h s := by
  unfold wt; split_ifs with h0
  · have := ds_le E πb ρb ρ πs hC h s
    rw [h0, mul_zero] at this
    rw [zero_mul]; exact le_antisymm (ds_nonneg E ρ πs h s) this
  · field_simp

/-- `w √N ≤ √(2 K C⋆ d⋆) + C⋆ √ι` on the count event. -/
theorem wt_sqrt_le {ι : ℝ} (hι : 0 ≤ ι) (h : Fin H) (s : S) {N : ℝ}
    (hN : N ≤ 2 * K * db E πb ρb πs h s + ι) :
    wt E πb ρb ρ πs h s * Real.sqrt N ≤
      Real.sqrt (2 * K * (concentrability E πb ρb ρ πs).toReal * ds E ρ πs h s) +
        (concentrability E πb ρb ρ πs).toReal * Real.sqrt ι := by
  set w := wt E πb ρb ρ πs h s
  set C := (concentrability E πb ρb ρ πs).toReal
  have hw0 := wt_nonneg E πb ρb ρ πs hC h s
  have hwC := wt_le E πb ρb ρ πs hC h s
  have hdb := db_nonneg E πb ρb πs h s
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : Real.sqrt N ≤ Real.sqrt (2 * K * db E πb ρb πs h s) + Real.sqrt ι :=
    (Real.sqrt_le_sqrt hN).trans (sqrt_add_le' (by positivity) hι)
  have h2 : w * Real.sqrt (2 * K * db E πb ρb πs h s) ≤ Real.sqrt (2 * K * C * ds E ρ πs h s) := by
    have e2 : w * Real.sqrt (2 * K * db E πb ρb πs h s) =
        Real.sqrt (w ^ 2 * (2 * K * db E πb ρb πs h s)) := by
      rw [Real.sqrt_mul (sq_nonneg w), Real.sqrt_sq hw0]
    rw [e2]
    refine Real.sqrt_le_sqrt ?_
    have e : w ^ 2 * (2 * K * db E πb ρb πs h s) = 2 * K * w * (w * db E πb ρb πs h s) := by ring
    rw [e, wt_mul_db E πb ρb ρ πs hC h s]
    have := ds_nonneg E ρ πs h s
    have : 2 * K * w * ds E ρ πs h s ≤ 2 * K * C * ds E ρ πs h s := by
      have := mul_le_mul_of_nonneg_right hwC (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * K) this)
      nlinarith
    exact this
  calc w * Real.sqrt N ≤ w * (Real.sqrt (2 * K * db E πb ρb πs h s) + Real.sqrt ι) :=
        mul_le_mul_of_nonneg_left h1 hw0
    _ = w * Real.sqrt (2 * K * db E πb ρb πs h s) + w * Real.sqrt ι := by ring
    _ ≤ _ := add_le_add h2 (mul_le_mul_of_nonneg_right hwC (Real.sqrt_nonneg ι))

end Weights

/-! ## Step 4(a): the gap is dominated by `f` -/

theorem gap_le_fK (hπs : IsOptimal E πs) (k : ℕ) (h : Fin H) (s : S) :
    max (optV E h.val s - (it E cb L sel π₀ x k).V h s) 0 ≤ fK E πs cb L sel π₀ x k h s := by
  have h1 := optV_eq_of_optimal hπs h s
  have h2 := Q_le_V cb L sel (rw' E) π₀ x k h s (πs h s)
  have h3 := V_nonneg cb L sel (rw' E) π₀ x k h s
  have h4 := optV_le_H E h.val s
  unfold fK Qs
  refine le_min (max_le_max (by simp only [it] at *; linarith) le_rfl) (max_le (by
    simp only [it] at *; linarith) (Nat.cast_nonneg H))

theorem Gs_le_a1 (hπs : IsOptimal E πs) (h : Fin H) :
    Gs E ρ πs cb L sel π₀ x h.val ≤ ∑ k ∈ range K, a1 E ρ πs cb L sel π₀ x k h := by
  unfold Gs a1
  refine sum_le_sum fun k _ ↦ sum_le_sum fun s _ ↦ ?_
  have hV : Vh E cb L sel π₀ x k h.val s = (it E cb L sel π₀ x k).V h s := by
    simp [Vh, h.isLt]
  rw [hV]
  exact mul_le_mul_of_nonneg_left (gap_le_fK E πs cb L sel π₀ x hπs k h s)
    (ds_nonneg E ρ πs h s)

theorem sum_a2 (k : ℕ) (h : Fin H) :
    a2 E ρ πs cb L sel π₀ x k h =
      ∑ s, dstar E πs ρ (h.val + 1) s * max (optV E (h.val + 1) s - Vh E cb L sel π₀ x k (h.val + 1) s) 0 := by
  unfold a2 gK ds
  rw [(dstar_flow E πs ρ).step h]
  refine sum_congr rfl fun s _ ↦ ?_
  congr 2
  funext t
  rw [Vn_eq_Vh]

/-! ## Step 4(b,c): one row -/

theorem beta_zero : beta H cb L 0 = 0 := by simp [beta]

theorem beta_nonneg (hH : 0 < H) (hcb : 0 ≤ cb) (n : ℕ) : 0 ≤ beta H cb L n :=
  sum_nonneg fun i _ ↦ mul_nonneg (onlineQRateWeight_nonneg hH _ _) (penalty_nonneg hcb i)

/-- Per-visit bound (Step 4(b)). -/
theorem fK_visit_le (hH : 0 < H) (hcb : 0 ≤ cb) (hL : 0 ≤ L)
    (hup : ∀ (h : Fin H) (s : S) (a : A) (n : ℕ), 1 ≤ n → n ≤ K →
      mart E cb L sel π₀ x h s a n ≤ penalty cb L H n)
    (k : ℕ) (h : Fin H) (s : S) :
    fK E πs cb L sel π₀ x k h s ≤
      (if cnt (visA πs x h s) k = 0 then (H : ℝ) else 0) +
      ∑ j ∈ range k, (if visA πs x h s j then
        onlineQRateWeight H (cnt (visA πs x h s) k) (cnt (visA πs x h s) j + 1) *
          gK E πs cb L sel π₀ x j h s else 0) +
      2 * beta H cb L (cnt (visA πs x h s) k) := by
  set n := cnt (visA πs x h s) k
  have hsum0 : 0 ≤ ∑ j ∈ range k, (if visA πs x h s j then
      onlineQRateWeight H n (cnt (visA πs x h s) j + 1) * gK E πs cb L sel π₀ x j h s else 0) :=
    sum_nonneg fun j _ ↦ by
      split_ifs
      · exact mul_nonneg (onlineQRateWeight_nonneg hH _ _) (gK_nonneg E πs cb L sel π₀ x j h s)
      · exact le_rfl
  have hb0 := beta_nonneg cb L hH hcb n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [if_pos h0]
    have := fK_le_H E πs cb L sel π₀ x k h s
    linarith
  · rw [if_neg (by omega), zero_add]
    have hQ := Q_decomp E cb L sel π₀ x hH h s (πs h s) k hpos
    have hw := weight_sum_eq_one (H := H) (visA πs x h s) hH hpos
    have hm := hup h s (πs h s) n hpos (cnt_vis_le x h s _ k)
    have hpb := (beta_bounds' cb L hH hcb hL hpos).1
    -- `Q⋆ - Q^k = Σ η P(V⋆ - V^j) + M + β`
    have hPopt : ((E h).transition s (πs h s)).expectation (optV E (h.val + 1)) =
        ∑ j ∈ range k, (if visA πs x h s j then onlineQRateWeight H n (cnt (visA πs x h s) j + 1) *
          ((E h).transition s (πs h s)).expectation (optV E (h.val + 1)) else 0) := by
      calc _ = ((E h).transition s (πs h s)).expectation (optV E (h.val + 1)) * 1 := (mul_one _).symm
        _ = _ := by
          rw [← hw, mul_sum]
          refine sum_congr rfl fun j _ ↦ ?_
          split_ifs <;> ring
    have hdiff : ((E h).transition s (πs h s)).expectation (optV E (h.val + 1)) -
        ∑ j ∈ range k, (if visA πs x h s j then onlineQRateWeight H n (cnt (visA πs x h s) j + 1) *
          ((E h).transition s (πs h s)).expectation (Vn E cb L sel π₀ x j h) else 0) ≤
        ∑ j ∈ range k, (if visA πs x h s j then onlineQRateWeight H n (cnt (visA πs x h s) j + 1) *
          gK E πs cb L sel π₀ x j h s else 0) := by
      rw [hPopt, ← sum_sub_distrib]
      refine sum_le_sum fun j _ ↦ ?_
      split_ifs
      · rw [← mul_sub]
        refine mul_le_mul_of_nonneg_left ?_ (onlineQRateWeight_nonneg hH _ _)
        unfold gK
        rw [← FiniteDistribution.expectation_sub]
        exact FiniteDistribution.expectation_mono _ fun t ↦ le_max_left _ _
      · simp
    unfold fK Qs
    refine (min_le_left _ _).trans (max_le ?_ (by linarith))
    rw [hQ]
    linarith

/-- Summed row bound (Step 4(c)). -/
theorem row_sum_le (hH : 0 < H) (hcb : 0 ≤ cb) (hL : 0 ≤ L)
    (hup : ∀ (h : Fin H) (s : S) (a : A) (n : ℕ), 1 ≤ n → n ≤ K →
      mart E cb L sel π₀ x h s a n ≤ penalty cb L H n)
    (h : Fin H) (s : S) :
    ∑ k ∈ range K, (if visA πs x h s k then fK E πs cb L sel π₀ x k h s else 0) ≤
      H + (1 + 1 / (H : ℝ)) *
        ∑ k ∈ range K, (if visA πs x h s k then gK E πs cb L sel π₀ x k h s else 0) +
      8 * (cb * Real.sqrt ((H : ℝ) ^ 3 * L)) * Real.sqrt (cnt (visA πs x h s) K) := by
  set X := visA πs x h s
  set N := cnt X K
  set Cb := cb * Real.sqrt ((H : ℝ) ^ 3 * L)
  have hCb : 0 ≤ Cb := mul_nonneg hcb (Real.sqrt_nonneg _)
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  -- split the per-visit bound into three sums
  have hstep : ∑ k ∈ range K, (if X k then fK E πs cb L sel π₀ x k h s else 0) ≤
      ∑ k ∈ range K, (if X k then (if cnt X k = 0 then (H : ℝ) else 0) else 0) +
      ∑ k ∈ range K, (if X k then ∑ j ∈ range k, (if X j then
        onlineQRateWeight H (cnt X k) (cnt X j + 1) * gK E πs cb L sel π₀ x j h s else 0) else 0) +
      ∑ k ∈ range K, (if X k then 2 * beta H cb L (cnt X k) else 0) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_le_sum fun k _ ↦ ?_
    by_cases hx : X k
    · simp only [if_pos hx]
      exact fK_visit_le E πs cb L sel π₀ x hH hcb hL hup k h s
    · simp only [if_neg hx]; norm_num
  -- first sum: at most one first visit
  have h1 : ∑ k ∈ range K, (if X k then (if cnt X k = 0 then (H : ℝ) else 0) else 0) ≤ H := by
    rw [sum_range_visits X (fun i ↦ if i = 0 then (H : ℝ) else 0) K, sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hH0
  -- second sum: regroup and tail
  have h2 : ∑ k ∈ range K, (if X k then ∑ j ∈ range k, (if X j then
        onlineQRateWeight H (cnt X k) (cnt X j + 1) * gK E πs cb L sel π₀ x j h s else 0) else 0) ≤
      (1 + 1 / (H : ℝ)) * ∑ k ∈ range K, (if X k then gK E πs cb L sel π₀ x k h s else 0) := by
    rw [regroup X (fun n m ↦ onlineQRateWeight H n (m + 1)) (fun j ↦ gK E πs cb L sel π₀ x j h s) K,
      mul_sum]
    refine sum_le_sum fun j _ ↦ ?_
    split_ifs
    · have ht := tail_le hH (i := cnt X j + 1) (by omega) (cnt X K)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right ht (gK_nonneg E πs cb L sel π₀ x j h s)
    · simp
  -- third sum: Σ_{i<N} 2β_i ≤ 8 Cb √N
  have h3 : ∑ k ∈ range K, (if X k then 2 * beta H cb L (cnt X k) else 0) ≤
      8 * Cb * Real.sqrt N := by
    rw [sum_range_visits X (fun i ↦ 2 * beta H cb L i) K]
    have hle : ∑ i ∈ range N, 2 * beta H cb L i ≤ ∑ i ∈ range (N + 1), 2 * beta H cb L i := by
      rw [sum_range_succ]
      have := beta_nonneg cb L hH hcb N
      linarith
    refine hle.trans ?_
    rw [sum_range_succ', beta_zero, mul_zero, add_zero,
      sum_range_succ_shift (fun i ↦ 2 * beta H cb L i)]
    calc ∑ i ∈ Icc 1 N, 2 * beta H cb L i ≤ ∑ i ∈ Icc 1 N, 4 * Cb * (1 / Real.sqrt i) := by
          refine sum_le_sum fun i hi ↦ ?_
          have hi1 := (mem_Icc.1 hi).1
          have := (beta_bounds' cb L hH hcb hL (by omega : 0 < i)).2
          rw [penalty_eq cb L hL] at this
          have e : 2 * (Cb / Real.sqrt i) = 2 * Cb * (1 / Real.sqrt i) := by ring
          simp only [Cb] at e ⊢
          nlinarith
      _ = 4 * Cb * ∑ i ∈ Icc 1 N, 1 / Real.sqrt i := by rw [mul_sum]
      _ ≤ 4 * Cb * (2 * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left (qLearning_sum_reciprocalSqrt_le N) (by positivity)
      _ = 8 * Cb * Real.sqrt N := by ring
  linarith

/-! ## Step 4(d,e): one stage -/

/-- The stage remainder `R`. -/
noncomputable def remR (nS H K : ℕ) (cb L C ι : ℝ) : ℝ :=
  2 * H * nS * C + 8 * C * (H : ℝ) ^ 2 * ι +
    16 * (cb * Real.sqrt ((H : ℝ) ^ 3 * L)) *
      (Real.sqrt (2 * K * C * nS) + nS * C * Real.sqrt ι)

theorem stage_step (hH : 0 < H) (hcb : 0 ≤ cb) (hL : 0 ≤ L) {ι : ℝ} (hι : 0 ≤ ι)
    (hπs : IsOptimal E πs) (hC : concentrability E πb ρb ρ πs ≠ ⊤)
    (hG : GoodEv E πb ρb ρ πs cb L sel π₀ x (concentrability E πb ρb ρ πs).toReal ι)
    (h : Fin H) :
    Gs E ρ πs cb L sel π₀ x h.val ≤ (1 + 1 / (H : ℝ)) ^ 3 * Gs E ρ πs cb L sel π₀ x (h.val + 1) +
      remR (Fintype.card S) H K cb L (concentrability E πb ρb ρ πs).toReal ι := by
  set C := (concentrability E πb ρb ρ πs).toReal
  set Cb := cb * Real.sqrt ((H : ℝ) ^ 3 * L)
  have hCb : 0 ≤ Cb := mul_nonneg hcb (Real.sqrt_nonneg _)
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHinv0 : 0 ≤ 1 / (H : ℝ) := by positivity
  have hHinv1 : 1 / (H : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hH1
  set γ := 1 + 1 / (H : ℝ)
  set T1 := ∑ k ∈ range K, a1 E ρ πs cb L sel π₀ x k h
  set T2 := ∑ k ∈ range K, a2 E ρ πs cb L sel π₀ x k h
  set Y1 := ∑ k ∈ range K, Z1 E πb ρb ρ πs cb L sel π₀ x k h
  set Y2 := ∑ k ∈ range K, Z2 E πb ρb ρ πs cb L sel π₀ x k h
  have hT2 : T2 = Gs E ρ πs cb L sel π₀ x (h.val + 1) := by
    simp only [T2, sum_a2, Gs]
  have hG1 := Gs_le_a1 E ρ πs cb L sel π₀ x hπs h
  -- (d): Y1 ≤ H S C + γ Y2 + 8 Cb (√(2KCS) + S C √ι)
  have hY1 : Y1 ≤ H * Fintype.card S * C + γ * Y2 +
      8 * Cb * (Real.sqrt (2 * K * C * Fintype.card S) + Fintype.card S * C * Real.sqrt ι) := by
    have eY1 : Y1 = ∑ s, wt E πb ρb ρ πs h s *
        ∑ k ∈ range K, (if visA πs x h s k then fK E πs cb L sel π₀ x k h s else 0) := by
      simp only [Y1, Z1]; rw [sum_comm]
      refine sum_congr rfl fun s _ ↦ ?_
      rw [mul_sum]; refine sum_congr rfl fun k _ ↦ ?_; split_ifs <;> simp
    have eY2 : Y2 = ∑ s, wt E πb ρb ρ πs h s *
        ∑ k ∈ range K, (if visA πs x h s k then gK E πs cb L sel π₀ x k h s else 0) := by
      simp only [Y2, Z2]; rw [sum_comm]
      refine sum_congr rfl fun s _ ↦ ?_
      rw [mul_sum]; refine sum_congr rfl fun k _ ↦ ?_; split_ifs <;> simp
    have hrow : ∀ s, wt E πb ρb ρ πs h s *
        ∑ k ∈ range K, (if visA πs x h s k then fK E πs cb L sel π₀ x k h s else 0) ≤
        H * C + γ * (wt E πb ρb ρ πs h s *
          ∑ k ∈ range K, (if visA πs x h s k then gK E πs cb L sel π₀ x k h s else 0)) +
        8 * Cb * (Real.sqrt (2 * K * C * ds E ρ πs h s) + C * Real.sqrt ι) := by
      intro s
      have hw0 := wt_nonneg E πb ρb ρ πs hC h s
      have hwC := wt_le E πb ρb ρ πs hC h s
      have hr : ∑ k ∈ range K, (if visA πs x h s k then fK E πs cb L sel π₀ x k h s else 0) ≤
          H + γ * ∑ k ∈ range K, (if visA πs x h s k then gK E πs cb L sel π₀ x k h s else 0) +
          8 * Cb * Real.sqrt (cnt (visA πs x h s) K) := row_sum_le E πs cb L sel π₀ x hH hcb hL hG.up h s
      have hsq := wt_sqrt_le E πb ρb ρ πs hC hι h s (hG.cntb h s)
      have h1 := mul_le_mul_of_nonneg_left hr hw0
      have h2 : wt E πb ρb ρ πs h s * H ≤ H * C := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hwC (Nat.cast_nonneg H)
      have h3 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 8 * Cb)
      have e1 : wt E πb ρb ρ πs h s * (H + γ * ∑ k ∈ range K, (if visA πs x h s k then
          gK E πs cb L sel π₀ x k h s else 0) + 8 * Cb * Real.sqrt (cnt (visA πs x h s) K)) =
          wt E πb ρb ρ πs h s * H + γ * (wt E πb ρb ρ πs h s * ∑ k ∈ range K,
            (if visA πs x h s k then gK E πs cb L sel π₀ x k h s else 0)) +
          8 * Cb * (wt E πb ρb ρ πs h s * Real.sqrt (cnt (visA πs x h s) K)) := by ring
      rw [e1] at h1
      linarith
    rw [eY1, eY2]
    calc _ ≤ ∑ s, (H * C + γ * (wt E πb ρb ρ πs h s *
          ∑ k ∈ range K, (if visA πs x h s k then gK E πs cb L sel π₀ x k h s else 0)) +
          8 * Cb * (Real.sqrt (2 * K * C * ds E ρ πs h s) + C * Real.sqrt ι)) := sum_le_sum fun s _ ↦ hrow s
      _ = Fintype.card S * (H * C) + γ * (∑ s, wt E πb ρb ρ πs h s *
          ∑ k ∈ range K, (if visA πs x h s k then gK E πs cb L sel π₀ x k h s else 0)) +
          8 * Cb * (∑ s, Real.sqrt (2 * K * C * ds E ρ πs h s) + Fintype.card S * C * Real.sqrt ι) := by
          rw [sum_add_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum,
            ← mul_sum, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
          ring
      _ ≤ _ := by
          have hcs := StatisticalRL.OfflineVILCB.Theorem63.sum_sqrt_le (2 * K * C) (by positivity)
            (fun s ↦ ds E ρ πs h s) (fun s ↦ ds_nonneg E ρ πs h s)
          have hsum : ∑ s, ds E ρ πs h s = 1 := sum_dstar E πs ρ h.isLt.le
          rw [hsum, mul_one] at hcs
          have := mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ 8 * Cb)
          have e2 : 8 * Cb * (∑ s, Real.sqrt (2 * K * C * ds E ρ πs h s) +
              Fintype.card S * C * Real.sqrt ι) = 8 * Cb * (∑ s, Real.sqrt (2 * K * C * ds E ρ πs h s))
              + 8 * Cb * (Fintype.card S * C * Real.sqrt ι) := by ring
          have e3 : 8 * Cb * (Real.sqrt (2 * K * C * Fintype.card S) +
              Fintype.card S * C * Real.sqrt ι) = 8 * Cb * Real.sqrt (2 * K * C * Fintype.card S)
              + 8 * Cb * (Fintype.card S * C * Real.sqrt ι) := by ring
          have e4 : (Fintype.card S : ℝ) * (H * C) = H * Fintype.card S * C := by ring
          rw [e2, e3, e4]
          linarith
  have hm1 : (1 - 1 / (2 * (H : ℝ))) * T1 ≤ Y1 + 2 * C * (H : ℝ) ^ 2 * ι := hG.m1 h
  have hm2 : Y2 ≤ γ * T2 + C * (H : ℝ) ^ 2 * ι := hG.m2 h
  have hT1nn : 0 ≤ T1 := sum_nonneg fun k _ ↦ sum_nonneg fun s _ ↦
    mul_nonneg (ds_nonneg E ρ πs h s) (fK_nonneg E πs cb L sel π₀ x k h s)
  have hT2nn : 0 ≤ T2 := sum_nonneg fun k _ ↦ sum_nonneg fun s _ ↦
    mul_nonneg (ds_nonneg E ρ πs h s) (gK_nonneg E πs cb L sel π₀ x k h s)
  -- (e): combine
  set B := H * Fintype.card S * C + γ * (γ * T2 + C * (H : ℝ) ^ 2 * ι) +
      8 * Cb * (Real.sqrt (2 * K * C * Fintype.card S) + Fintype.card S * C * Real.sqrt ι) +
      2 * C * (H : ℝ) ^ 2 * ι
  have hB : (1 - 1 / (2 * (H : ℝ))) * T1 ≤ B := by
    have := mul_le_mul_of_nonneg_left hm2 (by positivity : (0 : ℝ) ≤ γ)
    simp only [B]; linarith
  have hT1 : T1 ≤ γ * B := by
    have hfac : 1 ≤ γ * (1 - 1 / (2 * (H : ℝ))) := by
      simp only [γ]
      have e : (1 + 1 / (H : ℝ)) * (1 - 1 / (2 * H)) = 1 + 1 / (2 * H) - 1 / (2 * H ^ 2) := by
        field_simp; ring
      rw [e]
      have hHH : (H : ℝ) ≤ H ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by positivity) hH1
      have : 1 / (2 * (H : ℝ) ^ 2) ≤ 1 / (2 * H) := by
        apply one_div_le_one_div_of_le (by positivity); linarith
      linarith
    have hγ0 : 0 ≤ γ := by positivity
    calc T1 ≤ γ * (1 - 1 / (2 * (H : ℝ))) * T1 := le_mul_of_one_le_left hT1nn hfac
      _ = γ * ((1 - 1 / (2 * (H : ℝ))) * T1) := by ring
      _ ≤ γ * B := mul_le_mul_of_nonneg_left hB hγ0
  have hγ2 : γ ≤ 2 := by simp only [γ]; linarith
  have hγ1 : 1 ≤ γ := by simp only [γ]; linarith
  rw [← hT2]
  refine hG1.trans (hT1.trans ?_)
  unfold remR
  simp only [B]
  have hsq0 : 0 ≤ Real.sqrt (2 * K * C * Fintype.card S) + Fintype.card S * C * Real.sqrt ι := by
    positivity
  have hS0 : (0 : ℝ) ≤ Fintype.card S := Nat.cast_nonneg _
  have e1 : γ * (γ * (γ * T2)) = γ ^ 3 * T2 := by ring
  have hγ0 : 0 ≤ γ := by linarith
  have hA : γ * (H * Fintype.card S * C) ≤ 2 * H * Fintype.card S * C := by
    have : 0 ≤ (H : ℝ) * Fintype.card S * C := by positivity
    calc _ ≤ 2 * ((H : ℝ) * Fintype.card S * C) := mul_le_mul_of_nonneg_right hγ2 this
      _ = _ := by ring
  have hQ0 : 0 ≤ C * (H : ℝ) ^ 2 * ι := by positivity
  have hγγ : γ * γ ≤ 2 * 2 := mul_le_mul hγ2 hγ2 hγ0 (by norm_num)
  have hB2 : γ * (γ * (C * (H : ℝ) ^ 2 * ι)) ≤ 4 * (C * (H : ℝ) ^ 2 * ι) := by
    calc _ = (γ * γ) * (C * (H : ℝ) ^ 2 * ι) := by ring
      _ ≤ (2 * 2) * (C * (H : ℝ) ^ 2 * ι) := mul_le_mul_of_nonneg_right hγγ hQ0
      _ = _ := by ring
  have hB3 : γ * (2 * C * (H : ℝ) ^ 2 * ι) ≤ 4 * (C * (H : ℝ) ^ 2 * ι) := by
    calc _ = γ * (2 * (C * (H : ℝ) ^ 2 * ι)) := by ring
      _ ≤ 2 * (2 * (C * (H : ℝ) ^ 2 * ι)) :=
        mul_le_mul_of_nonneg_right hγ2 (by positivity)
      _ = _ := by ring
  have hB4 : γ * (8 * Cb * (Real.sqrt (2 * K * C * Fintype.card S) +
      Fintype.card S * C * Real.sqrt ι)) ≤ 16 * Cb * (Real.sqrt (2 * K * C * Fintype.card S) +
      Fintype.card S * C * Real.sqrt ι) := by
    have : 0 ≤ 8 * Cb * (Real.sqrt (2 * K * C * Fintype.card S) +
      Fintype.card S * C * Real.sqrt ι) := by positivity
    calc _ ≤ 2 * (8 * Cb * (Real.sqrt (2 * K * C * Fintype.card S) +
          Fintype.card S * C * Real.sqrt ι)) := mul_le_mul_of_nonneg_right hγ2 this
      _ = _ := by ring
  have eL : γ * (H * Fintype.card S * C + γ * (γ * T2 + C * (H : ℝ) ^ 2 * ι) +
      8 * Cb * (Real.sqrt (2 * K * C * Fintype.card S) + Fintype.card S * C * Real.sqrt ι) +
      2 * C * (H : ℝ) ^ 2 * ι) = γ * (H * Fintype.card S * C) + γ * (γ * (γ * T2)) +
      γ * (γ * (C * (H : ℝ) ^ 2 * ι)) + γ * (8 * Cb * (Real.sqrt (2 * K * C * Fintype.card S) +
      Fintype.card S * C * Real.sqrt ι)) + γ * (2 * C * (H : ℝ) ^ 2 * ι) := by ring
  have eR : (1 + 1 / (H : ℝ)) ^ 3 * T2 + (2 * H * Fintype.card S * C + 8 * C * (H : ℝ) ^ 2 * ι +
      16 * (cb * Real.sqrt ((H : ℝ) ^ 3 * L)) * (Real.sqrt (2 * K * C * Fintype.card S) +
        Fintype.card S * C * Real.sqrt ι)) = γ ^ 3 * T2 + 2 * H * Fintype.card S * C +
      4 * (C * (H : ℝ) ^ 2 * ι) + 4 * (C * (H : ℝ) ^ 2 * ι) + 16 * Cb *
      (Real.sqrt (2 * K * C * Fintype.card S) + Fintype.card S * C * Real.sqrt ι) := by
    simp only [γ, Cb]; ring
  rw [eL, eR]
  linarith

/-! ## Step 4(f) and the gap -/

theorem Gs_top : Gs E ρ πs cb L sel π₀ x H = 0 := by
  unfold Gs
  refine sum_eq_zero fun k _ ↦ sum_eq_zero fun s _ ↦ ?_
  simp [Vh, optV_of_ge E (le_refl H)]

theorem Gs_zero_le (hH : 0 < H) (hcb : 0 ≤ cb) (hL : 0 ≤ L) {ι : ℝ} (hι : 0 ≤ ι)
    (hπs : IsOptimal E πs) (hC : concentrability E πb ρb ρ πs ≠ ⊤)
    (hG : GoodEv E πb ρb ρ πs cb L sel π₀ x (concentrability E πb ρb ρ πs).toReal ι) :
    Gs E ρ πs cb L sel π₀ x 0 ≤
      21 * H * remR (Fintype.card S) H K cb L (concentrability E πb ρb ρ πs).toReal ι := by
  set R := remR (Fintype.card S) H K cb L (concentrability E πb ρb ρ πs).toReal ι
  set γ := (1 + 1 / (H : ℝ)) ^ 3
  have hC0 : 0 ≤ (concentrability E πb ρb ρ πs).toReal := ENNReal.toReal_nonneg
  have hR0 : 0 ≤ R := by simp only [R, remR]; positivity
  have hHi : (0 : ℝ) ≤ 1 / (H : ℝ) := by positivity
  have hγ1 : 1 ≤ γ := one_le_pow₀ (by linarith)
  have key : ∀ m, m ≤ H → Gs E ρ πs cb L sel π₀ x (H - m) ≤ m * γ ^ m * R := by
    intro m
    induction m with
    | zero => intro _; simp [Gs_top]
    | succ m ih =>
      intro hm
      have hh : H - (m + 1) < H := by omega
      have hs := stage_step E πb ρb ρ πs cb L sel π₀ x hH hcb hL hι hπs hC hG ⟨H - (m + 1), hh⟩
      simp only at hs
      rw [show H - (m + 1) + 1 = H - m by omega] at hs
      have ih' := ih (by omega)
      have hγm : 1 ≤ γ ^ m := one_le_pow₀ hγ1
      have e : γ * (m * γ ^ m * R) = m * γ ^ (m + 1) * R := by ring
      have hR' : R ≤ γ ^ (m + 1) * R := le_mul_of_one_le_left hR0 (one_le_pow₀ hγ1)
      have hfin : γ * (m * γ ^ m * R) + R ≤ ((m + 1 : ℕ) : ℝ) * γ ^ (m + 1) * R := by
        rw [e]; push_cast; linarith
      have hγ0 : 0 ≤ γ := by linarith
      have := mul_le_mul_of_nonneg_left ih' hγ0
      linarith
  have h0 := key H le_rfl
  rw [Nat.sub_self] at h0
  have hpow : γ ^ H ≤ 21 := by
    simp only [γ]; rw [← pow_mul]
    exact StatisticalRL.OfflineRL.LCBQ.one_add_inv_pow_le H hH
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  calc _ ≤ (H : ℝ) * γ ^ H * R := h0
    _ ≤ (H : ℝ) * 21 * R := by
        apply mul_le_mul_of_nonneg_right _ hR0
        exact mul_le_mul_of_nonneg_left hpow hH0
    _ = 21 * H * R := by ring

/-- **Deterministic gap bound**: on the good event, the output's gap is at most `21 H R / K`. -/
theorem gap_le (hH : 0 < H) (hK : 0 < K) (hcb : 0 ≤ cb) (hL : 0 ≤ L) {ι : ℝ} (hι : 0 ≤ ι)
    (hπs : IsOptimal E πs) (hC : concentrability E πb ρb ρ πs ≠ ⊤)
    (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (hG : GoodEv E πb ρb ρ πs cb L sel π₀ x (concentrability E πb ρb ρ πs).toReal ι) :
    ρ.expectation (optV E 0) - ρ.expectation (polV E (it E cb L sel π₀ x K).pol 0) ≤
      21 * H * remR (Fintype.card S) H K cb L (concentrability E πb ρb ρ πs).toReal ι / K := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have h0 : (0 : ℕ) < H := hH
  have hpes : ∀ s, optV E 0 s - polV E (it E cb L sel π₀ x K).pol 0 s ≤
      optV E 0 s - (it E cb L sel π₀ x K).V ⟨0, h0⟩ s := by
    intro s
    have := V_le_polV E cb L sel π₀ x hH hcb hL hG.low hsel K ⟨0, h0⟩ s
    simp only at this; linarith
  have havg : ∀ s, optV E 0 s - (it E cb L sel π₀ x K).V ⟨0, h0⟩ s ≤
      (1 / K) * ∑ k ∈ range K, max (optV E 0 s - Vh E cb L sel π₀ x k 0 s) 0 := by
    intro s
    have hk : ∀ k ∈ range K, optV E 0 s - (it E cb L sel π₀ x K).V ⟨0, h0⟩ s ≤
        max (optV E 0 s - Vh E cb L sel π₀ x k 0 s) 0 := by
      intro k hk
      have := V_mono cb L sel (rw' E) π₀ x (mem_range.1 hk).le ⟨0, h0⟩ s
      simp only [Vh, dif_pos h0]
      simp only [it] at this ⊢
      exact le_max_of_le_left (by linarith)
    have := sum_le_sum hk
    rw [sum_const, card_range, nsmul_eq_mul] at this
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hK0]
    linarith
  have hd0 : ∀ s, dstar E πs ρ 0 s = ρ.prob s := (dstar_flow E πs ρ).init
  calc ρ.expectation (optV E 0) - ρ.expectation (polV E (it E cb L sel π₀ x K).pol 0)
      = ∑ s, ρ.prob s * (optV E 0 s - polV E (it E cb L sel π₀ x K).pol 0 s) := by
        simp only [FiniteDistribution.expectation, ← sum_sub_distrib, mul_sub]
    _ ≤ ∑ s, ρ.prob s * ((1 / K) * ∑ k ∈ range K, max (optV E 0 s - Vh E cb L sel π₀ x k 0 s) 0) :=
        sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left ((hpes s).trans (havg s)) (ρ.prob_nonneg s)
    _ = (1 / K) * Gs E ρ πs cb L sel π₀ x 0 := by
        unfold Gs
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun s _ ↦ ?_
        rw [hd0, mul_sum, mul_sum, mul_sum]
        refine sum_congr rfl fun k _ ↦ ?_
        ring
    _ ≤ (1 / K) * (21 * H * remR (Fintype.card S) H K cb L (concentrability E πb ρb ρ πs).toReal ι) :=
        mul_le_mul_of_nonneg_left (Gs_zero_le E πb ρb ρ πs cb L sel π₀ x hH hcb hL hι hπs hC hG)
          (by positivity)
    _ = _ := by ring

end StatisticalRL.LCBQFinite

import Formalization.OfflineRL.FiniteVILCB.RowEvents
import Formalization.Probability.Variance

/-!
# Deterministic analysis on the good event

Plan §3.1: dominance (Dom), pessimism (D1), the gap reduction (D2, unrolled along the optimal
state flow), and the finite-horizon occupancy-weighted variance bound (D3). Everything here is
pathwise: the statistics `cnt, row` are arbitrary, subject to the row event `RowGood` at visited
triples.
-/

open scoped BigOperators

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

section Values

variable {H : ℕ} (E : Fin H → EnvironmentStage S A)

theorem optV_of_lt (h : Fin H) (s : S) :
    optV E h.val s = actionMaximum (fun a ↦ (E h).reward s a +
      ((E h).transition s a).expectation (optV E (h.val + 1))) := by
  rw [optV, dif_pos h.isLt]

theorem optV_of_ge {h : ℕ} (hh : H ≤ h) (s : S) : optV E h s = 0 := by
  rw [optV, dif_neg (by omega)]

theorem polV_of_lt (π : Fin H → S → A) (h : Fin H) (s : S) :
    polV E π h.val s = (E h).reward s (π h s) +
      ((E h).transition s (π h s)).expectation (polV E π (h.val + 1)) := by
  rw [polV, dif_pos h.isLt]

theorem polV_of_ge (π : Fin H → S → A) {h : ℕ} (hh : H ≤ h) (s : S) : polV E π h s = 0 := by
  rw [polV, dif_neg (by omega)]

theorem polV_nonneg (π : Fin H → S → A) : ∀ h s, 0 ≤ polV E π h s := by
  refine backward_induction (H := H) (P := fun h ↦ ∀ s, 0 ≤ polV E π h s) ?_ ?_
  · intro h hh s
    rw [polV_of_ge E π hh]
  · intro h hh ih s
    have := polV_of_lt E π ⟨h, hh⟩ s
    simp only at this
    rw [this]
    exact add_nonneg ((E _).reward_nonneg _ _) (FiniteDistribution.expectation_nonneg _ ih)

end Values

section Analysis

variable {H : ℕ} (E : Fin H → EnvironmentStage S A) (cb ι L : ℝ)
  (cnt : Fin H → S → A → ℕ) (row : Fin H → S → A → FiniteDistribution S)

/-- Shorthand for the estimated values. -/
noncomputable abbrev vh (E : Fin H → EnvironmentStage S A) (cb ι : ℝ) (cnt : Fin H → S → A → ℕ)
    (row : Fin H → S → A → FiniteDistribution S) : ℕ → S → ℝ :=
  vhatGen cb ι (fun h ↦ (E h).reward) cnt row

/-- The penalty at `(h,s,a)`. -/
noncomputable def pen (h : Fin H) (s : S) (a : A) : ℝ :=
  bonus cb ι H (cnt h s a) (row h s a) (vhatGen cb ι (fun h ↦ (E h).reward) cnt row (h.val + 1))

/-- Hypotheses of the deterministic analysis. -/
structure Good : Prop where
  cb16 : 16 ≤ cb
  L0 : 0 ≤ L
  Lι : L ≤ ι
  rows : ∀ h s a, 0 < cnt h s a → RowGood H L (cnt h s a) (row h s a) ((E h).transition s a)
    (vhatGen cb ι (fun h ↦ (E h).reward) cnt row (h.val + 1))

variable {E cb ι L cnt row}

theorem Good.cb0 (hG : Good E cb ι L cnt row) : 0 ≤ cb := by linarith [hG.cb16]
theorem Good.ι0 (hG : Good E cb ι L cnt row) : 0 ≤ ι := hG.L0.trans hG.Lι

theorem Good.bounds (hG : Good E cb ι L cnt row) (h : ℕ) (s : S) :
    0 ≤ vh E cb ι cnt row h s ∧ vh E cb ι cnt row h s ≤ ((H - h : ℕ) : ℝ) :=
  vhatGen_bounds cb ι _ cnt row hG.cb0 hG.ι0 (fun h ↦ (E h).reward_nonneg)
    (fun h ↦ (E h).reward_le_one) h s

theorem abs_expectation_sub_le_vmax (q P : FiniteDistribution S) {V : S → ℝ}
    (hV : ∀ s, 0 ≤ V s) : |q.expectation V - P.expectation V| ≤ vmax V := by
  have h1 : q.expectation V ≤ vmax V := q.expectation_le_const fun s ↦ le_vmax V s
  have h2 : P.expectation V ≤ vmax V := P.expectation_le_const fun s ↦ le_vmax V s
  have h3 : 0 ≤ q.expectation V := q.expectation_nonneg hV
  have h4 : 0 ≤ P.expectation V := P.expectation_nonneg hV
  rw [abs_le]
  constructor <;> linarith

/-- **(Dom)** The penalty dominates the estimation error of `V̂_{h+1}`. -/
theorem Good.dom (hG : Good E cb ι L cnt row) (h : Fin H) (s : S) (a : A) :
    |(row h s a).expectation (vh E cb ι cnt row (h.val + 1)) -
      ((E h).transition s a).expectation (vh E cb ι cnt row (h.val + 1))| ≤ pen E cb ι cnt row h s a := by
  have hV0 : ∀ t, 0 ≤ vh E cb ι cnt row (h.val + 1) t := fun t ↦ (hG.bounds _ t).1
  have hvm := abs_expectation_sub_le_vmax (row h s a) ((E h).transition s a) hV0
  unfold pen bonus
  split_ifs with hc
  · exact hvm
  · refine le_min ?_ hvm
    have hpos : 0 < cnt h s a := Nat.pos_of_ne_zero hc
    obtain ⟨hr1, -⟩ := hG.rows h s a hpos
    set q := row h s a
    set V := vh E cb ι cnt row (h.val + 1)
    set N : ℝ := (cnt h s a : ℝ)
    have hN : 0 < N := Nat.cast_pos.mpr hpos
    have hv : 0 ≤ q.variance V := q.variance_nonneg V
    have hx : 2 * Real.sqrt (4 * q.variance V * L / N) ≤ Real.sqrt (cb * ι * q.variance V / N) := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_le_sqrt
      have h16 : 4 * (4 * q.variance V * L / N) = (16 * L) * q.variance V / N := by ring
      rw [h16]
      apply div_le_div_of_nonneg_right _ hN.le
      have : 16 * L ≤ cb * ι := by nlinarith [hG.cb16, hG.Lι, hG.L0]
      nlinarith
    have hy : 2 * (5 * H * L / N) ≤ cb * H * ι / N := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hN.le
      have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg _
      have : 10 * L ≤ cb * ι := by nlinarith [hG.cb16, hG.Lι, hG.L0]
      nlinarith
    calc |q.expectation V - ((E h).transition s a).expectation V|
        ≤ Real.sqrt (4 * q.variance V * L / N) + 5 * H * L / N := hr1
      _ ≤ (Real.sqrt (cb * ι * q.variance V / N) + cb * H * ι / N) / 2 := by linarith
      _ ≤ max (Real.sqrt (cb * ι * q.variance V / N)) (cb * H * ι / N) := by
          have := le_max_left (Real.sqrt (cb * ι * q.variance V / N)) (cb * H * ι / N)
          have := le_max_right (Real.sqrt (cb * ι * q.variance V / N)) (cb * H * ι / N)
          linarith

theorem pen_nonneg (hG : Good E cb ι L cnt row) (h : Fin H) (s : S) (a : A) :
    0 ≤ pen E cb ι cnt row h s a :=
  bonus_nonneg (H := H) cb ι hG.cb0 hG.ι0 _ _ fun t ↦ (hG.bounds _ t).1

theorem pen_le_H (hG : Good E cb ι L cnt row) (h : Fin H) (s : S) (a : A) :
    pen E cb ι cnt row h s a ≤ H :=
  (bonus_le_vmax (H := H) cb ι _ _ _).trans (vmax_le fun t ↦ (hG.bounds _ t).2.trans
    (Nat.cast_le.mpr (Nat.sub_le H (h.val + 1))))

/-- Greedy policies for `Q̂`. -/
def IsGreedy (cnt : Fin H → S → A → ℕ) (row : Fin H → S → A → FiniteDistribution S)
    (π : Fin H → S → A) : Prop :=
  ∀ h s a, qhatGen cb ι (fun h ↦ (E h).reward) cnt row h s a ≤
    qhatGen cb ι (fun h ↦ (E h).reward) cnt row h s (π h s)

theorem vhat_eq_greedy {π : Fin H → S → A} (hπ : IsGreedy (E := E) (cb := cb) (ι := ι) cnt row π)
    (h : Fin H) (s : S) :
    vh E cb ι cnt row h.val s = qhatGen cb ι (fun h ↦ (E h).reward) cnt row h s (π h s) := by
  unfold vh
  rw [vhatGen_of_lt]
  exact le_antisymm (actionMaximum_le fun a ↦ hπ h s a) (le_actionMaximum _ _)

/-- **(D1) Pessimism.** -/
theorem Good.pessimism (hG : Good E cb ι L cnt row) {π : Fin H → S → A}
    (hπ : IsGreedy (E := E) (cb := cb) (ι := ι) cnt row π) : ∀ h s, vh E cb ι cnt row h s ≤ polV E π h s := by
  refine backward_induction (H := H) (P := fun h ↦ ∀ s, vh E cb ι cnt row h s ≤ polV E π h s) ?_ ?_
  · intro h hh s
    unfold vh
    rw [vhatGen_of_ge _ _ _ _ _ hh, polV_of_ge E π hh]
  · intro h hh ih s
    have e := vhat_eq_greedy hπ ⟨h, hh⟩ s
    have p := polV_of_lt E π ⟨h, hh⟩ s
    simp only at e p
    rw [e, p]
    unfold qhatGen
    apply max_le
    · have hd := hG.dom ⟨h, hh⟩ s (π ⟨h, hh⟩ s)
      have hmono : ((E ⟨h, hh⟩).transition s (π ⟨h, hh⟩ s)).expectation (vh E cb ι cnt row (h + 1)) ≤
          ((E ⟨h, hh⟩).transition s (π ⟨h, hh⟩ s)).expectation (polV E π (h + 1)) :=
        FiniteDistribution.expectation_mono _ ih
      unfold pen at hd
      simp only at hd hmono ⊢
      have := (abs_le.mp hd).2
      linarith
    · have := polV_nonneg E π (h + 1)
      exact add_nonneg ((E _).reward_nonneg _ _) (FiniteDistribution.expectation_nonneg _ this)

/-- Lower bound used by (D2) and (D3): `V̂_h(s) ≥ r + P⋆V̂_{h+1} - 2b⋆`. -/
theorem Good.vhat_lower (hG : Good E cb ι L cnt row) (h : Fin H) (s : S) (a : A) :
    (E h).reward s a + ((E h).transition s a).expectation (vh E cb ι cnt row (h.val + 1)) -
      2 * pen E cb ι cnt row h s a ≤ vh E cb ι cnt row h.val s := by
  unfold vh
  rw [vhatGen_of_lt]
  refine le_trans ?_ (le_actionMaximum _ a)
  unfold qhatGen
  refine le_trans ?_ (le_max_left _ _)
  have hd := (abs_le.mp (hG.dom h s a)).1
  unfold pen at hd ⊢
  linarith

/-- Optimal policy: `π⋆` attains the maximum of `Q⋆`. -/
def IsOptimal (E : Fin H → EnvironmentStage S A) (πs : Fin H → S → A) : Prop :=
  ∀ h s a, (E h).reward s a + ((E h).transition s a).expectation (optV E (h.val + 1)) ≤
    (E h).reward s (πs h s) + ((E h).transition s (πs h s)).expectation (optV E (h.val + 1))

theorem optV_eq_of_optimal {πs : Fin H → S → A} (hπs : IsOptimal E πs) (h : Fin H) (s : S) :
    optV E h.val s = (E h).reward s (πs h s) +
      ((E h).transition s (πs h s)).expectation (optV E (h.val + 1)) := by
  rw [optV_of_lt]
  exact le_antisymm (actionMaximum_le fun a ↦ hπs h s a)
    (le_actionMaximum (fun a ↦ (E h).reward s a +
      ((E h).transition s a).expectation (optV E (h.val + 1))) (πs h s))

/-- **(D2)** One-step gap recursion along `π⋆`. -/
theorem Good.gap_step (hG : Good E cb ι L cnt row) {πs : Fin H → S → A} (hπs : IsOptimal E πs)
    (h : Fin H) (s : S) :
    optV E h.val s - vh E cb ι cnt row h.val s ≤ ((E h).transition s (πs h s)).expectation
      (fun t ↦ optV E (h.val + 1) t - vh E cb ι cnt row (h.val + 1) t) + 2 * pen E cb ι cnt row h s (πs h s) := by
  rw [optV_eq_of_optimal hπs, FiniteDistribution.expectation_sub]
  have := hG.vhat_lower h s (πs h s)
  linarith

/-! ## Unrolling along a state flow -/

/-- A state flow for `π⋆` started at `ρ`: `d_0 = ρ`, `d_{h+1} = d_h P⋆_h`. -/
structure Flow (E : Fin H → EnvironmentStage S A) (πs : Fin H → S → A) (ρ : FiniteDistribution S)
    (d : ℕ → S → ℝ) : Prop where
  init : ∀ s, d 0 s = ρ.prob s
  nonneg : ∀ h s, 0 ≤ d h s
  step : ∀ (h : Fin H) (f : S → ℝ), ∑ s, d (h.val + 1) s * f s =
    ∑ s, d h.val s * ((E h).transition s (πs h s)).expectation f

variable (E cb ι cnt row) in
/-- Stage penalty mass `B_h = ⟨d_h, b⋆_h⟩` (zero for `h ≥ H`). -/
noncomputable def stageB (πs : Fin H → S → A) (d : ℕ → S → ℝ) (h : ℕ) : ℝ :=
  if hh : h < H then ∑ s, d h s * pen E cb ι cnt row ⟨h, hh⟩ s (πs ⟨h, hh⟩ s) else 0

theorem Good.gap_unroll (hG : Good E cb ι L cnt row) {πs : Fin H → S → A} (hπs : IsOptimal E πs)
    {ρ : FiniteDistribution S} {d : ℕ → S → ℝ} (hd : Flow E πs ρ d) :
    ∀ k, k ≤ H → ∑ s, d (H - k) s * (optV E (H - k) s - vh E cb ι cnt row (H - k) s) ≤
      2 * ∑ h ∈ Finset.Ico (H - k) H, stageB E cb ι cnt row πs d h := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [vh, optV_of_ge E le_rfl, vhatGen_of_ge _ _ _ _ _ (le_refl H)]
  | succ k ih =>
    intro hk
    have hlt : H - (k + 1) < H := by omega
    set h : Fin H := ⟨H - (k + 1), hlt⟩
    have hh1 : h.val + 1 = H - k := by simp [h]; omega
    have hIco : Finset.Ico (H - (k + 1)) H = insert (H - (k + 1)) (Finset.Ico (H - k) H) := by
      rw [show H - k = H - (k + 1) + 1 by omega, Nat.Ico_insert_succ_left hlt]
    rw [hIco, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega)]
    have hstep := hd.step h (fun t ↦ optV E (h.val + 1) t - vh E cb ι cnt row (h.val + 1) t)
    have hrec := ih (by omega)
    have hB : stageB E cb ι cnt row πs d (H - (k + 1)) =
        ∑ s, d h.val s * pen E cb ι cnt row h s (πs h s) := by
      simp [stageB, hlt, h]
    calc ∑ s, d (H - (k + 1)) s * (optV E (H - (k + 1)) s - vh E cb ι cnt row (H - (k + 1)) s)
        = ∑ s, d h.val s * (optV E h.val s - vh E cb ι cnt row h.val s) := rfl
      _ ≤ ∑ s, d h.val s * (((E h).transition s (πs h s)).expectation
            (fun t ↦ optV E (h.val + 1) t - vh E cb ι cnt row (h.val + 1) t) +
              2 * pen E cb ι cnt row h s (πs h s)) :=
          Finset.sum_le_sum fun s _ ↦
            mul_le_mul_of_nonneg_left (hG.gap_step hπs h s) (hd.nonneg _ _)
      _ = ∑ s, d (H - k) s * (optV E (H - k) s - vh E cb ι cnt row (H - k) s) +
            2 * ∑ s, d h.val s * pen E cb ι cnt row h s (πs h s) := by
          rw [← hh1, hstep, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          ring
      _ ≤ 2 * (stageB E cb ι cnt row πs d (H - (k + 1)) +
            ∑ x ∈ Finset.Ico (H - k) H, stageB E cb ι cnt row πs d x) := by
          rw [hB]
          linarith

/-- **Gap bound** `V⋆_0(ρ) - V^{π̂}_0(ρ) ≤ 2 B`. -/
theorem Good.gap_le (hG : Good E cb ι L cnt row) {πs : Fin H → S → A} (hπs : IsOptimal E πs)
    {ρ : FiniteDistribution S} {d : ℕ → S → ℝ} (hd : Flow E πs ρ d) {π : Fin H → S → A}
    (hπ : IsGreedy (E := E) (cb := cb) (ι := ι) cnt row π) :
    ρ.expectation (optV E 0) - ρ.expectation (polV E π 0) ≤
      2 * ∑ h ∈ Finset.range H, stageB E cb ι cnt row πs d h := by
  have h0 := hG.gap_unroll hπs hd H le_rfl
  simp only [Nat.sub_self, Finset.range_eq_Ico] at h0 ⊢
  refine le_trans ?_ h0
  rw [← FiniteDistribution.expectation_sub]
  unfold FiniteDistribution.expectation
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [hd.init s]
  apply mul_le_mul_of_nonneg_left _ (ρ.prob_nonneg s)
  linarith [hG.pessimism hπ 0 s]

/-! ## (D3) Occupancy-weighted variance -/

theorem Good.var_step (hG : Good E cb ι L cnt row) {πs : Fin H → S → A} (h : Fin H) (s : S) :
    ((E h).transition s (πs h s)).variance (vh E cb ι cnt row (h.val + 1)) ≤
      ((E h).transition s (πs h s)).expectation (fun t ↦ vh E cb ι cnt row (h.val + 1) t ^ 2) - vh E cb ι cnt row h.val s ^ 2 +
        2 * H * (vh E cb ι cnt row h.val s - ((E h).transition s (πs h s)).expectation (vh E cb ι cnt row (h.val + 1)) +
          2 * pen E cb ι cnt row h s (πs h s)) := by
  set P := (E h).transition s (πs h s)
  set v := vh E cb ι cnt row h.val s
  set e := P.expectation (vh E cb ι cnt row (h.val + 1))
  set b := pen E cb ι cnt row h s (πs h s)
  have hlow := hG.vhat_lower h s (πs h s)
  have hx : 0 ≤ v - e + 2 * b := by
    have := (E h).reward_nonneg s (πs h s)
    simp only [v, e, b, P] at hlow ⊢
    linarith
  have hv := hG.bounds h.val s
  have he0 : 0 ≤ e := P.expectation_nonneg fun t ↦ (hG.bounds _ t).1
  have hle : ((H - h.val : ℕ) : ℝ) ≤ H := by exact_mod_cast Nat.sub_le _ _
  have he1 : e ≤ H := (P.expectation_le_const fun t ↦ (hG.bounds _ t).2).trans
    (by exact_mod_cast Nat.sub_le _ _)
  have hy : v + e ≤ 2 * H := by linarith [hv.2]
  unfold FiniteDistribution.variance
  -- v² - e² = (v - e)(v + e) ≤ (v - e + 2b)(v + e) ≤ 2H (v - e + 2b)
  have hb : 0 ≤ b := pen_nonneg hG h s _
  have key : v ^ 2 - e ^ 2 ≤ 2 * H * (v - e + 2 * b) := by
    have h1 : v ^ 2 - e ^ 2 = (v - e) * (v + e) := by ring
    have h2 : (v - e) * (v + e) ≤ (v - e + 2 * b) * (v + e) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith [hv.1])
    have h3 : (v - e + 2 * b) * (v + e) ≤ (v - e + 2 * b) * (2 * H) :=
      mul_le_mul_of_nonneg_left hy hx
    nlinarith
  linarith

/-- **(D3)** `Σ_h ⟨d_h, Var_{P⋆_h}(V̂_{h+1})⟩ ≤ 2H² + 4H·B`. -/
theorem Good.variance_sum (hG : Good E cb ι L cnt row) {πs : Fin H → S → A}
    {ρ : FiniteDistribution S} {d : ℕ → S → ℝ} (hd : Flow E πs ρ d) :
    ∑ h : Fin H, ∑ s, d h.val s * ((E h).transition s (πs h s)).variance (vh E cb ι cnt row (h.val + 1)) ≤
      2 * (H : ℝ) ^ 2 + 4 * H * ∑ h ∈ Finset.range H, stageB E cb ι cnt row πs d h := by
  -- T_h = ⟨d_h, V̂_h² - 2H V̂_h⟩
  let T : ℕ → ℝ := fun h ↦ ∑ s, d h s * (vh E cb ι cnt row h s ^ 2 - 2 * H * vh E cb ι cnt row h s)
  have hstage : ∀ h : Fin H, ∑ s, d h.val s * ((E h).transition s (πs h s)).variance
      (vh E cb ι cnt row (h.val + 1)) ≤ T (h.val + 1) - T h.val + 4 * H * stageB E cb ι cnt row πs d h.val := by
    intro h
    have hT1 : T (h.val + 1) = ∑ s, d h.val s * ((E h).transition s (πs h s)).expectation
        (fun t ↦ vh E cb ι cnt row (h.val + 1) t ^ 2 - 2 * H * vh E cb ι cnt row (h.val + 1) t) := hd.step h _
    have hB : stageB E cb ι cnt row πs d h.val =
        ∑ s, d h.val s * pen E cb ι cnt row h s (πs h s) := by simp [stageB, h.isLt]
    rw [hT1, hB, Finset.mul_sum]
    simp only [T]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s _ ↦ ?_
    have hvs := hG.var_step (πs := πs) h s
    rw [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_mul] at *
    have hdn := hd.nonneg h.val s
    have := mul_le_mul_of_nonneg_left hvs hdn
    nlinarith [this]
  have hsum : ∀ k, k ≤ H → ∑ h ∈ Finset.range k, (if hh : h < H then
      ∑ s, d h s * ((E ⟨h, hh⟩).transition s (πs ⟨h, hh⟩ s)).variance (vh E cb ι cnt row (h + 1)) else 0) ≤
      T k - T 0 + 4 * H * ∑ h ∈ Finset.range k, stageB E cb ι cnt row πs d h := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkH : k < H := by omega
      rw [Finset.sum_range_succ, Finset.sum_range_succ, dif_pos hkH]
      have := hstage ⟨k, hkH⟩
      have := ih (by omega)
      simp only at *
      nlinarith
  have hH := hsum H le_rfl
  have hconv : ∑ h : Fin H, ∑ s, d h.val s * ((E h).transition s (πs h s)).variance
      (vh E cb ι cnt row (h.val + 1)) = ∑ h ∈ Finset.range H, (if hh : h < H then
      ∑ s, d h s * ((E ⟨h, hh⟩).transition s (πs ⟨h, hh⟩ s)).variance (vh E cb ι cnt row (h + 1)) else 0) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [dif_pos h.isLt]
  rw [hconv]
  refine hH.trans ?_
  have hTH : T H = 0 := by simp [T, vh, vhatGen_of_ge _ _ _ _ _ (le_refl H)]
  have hT0 : -T 0 ≤ 2 * (H : ℝ) ^ 2 := by
    simp only [T]
    rw [← Finset.sum_neg_distrib]
    calc ∑ s, -(d 0 s * (vh E cb ι cnt row 0 s ^ 2 - 2 * H * vh E cb ι cnt row 0 s)) ≤ ∑ s, ρ.prob s * (2 * (H : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun s _ ↦ ?_
          rw [hd.init s]
          have hb := hG.bounds 0 s
          simp only [Nat.sub_zero] at hb
          have hp := ρ.prob_nonneg s
          have : -(vh E cb ι cnt row 0 s ^ 2 - 2 * H * vh E cb ι cnt row 0 s) ≤ 2 * (H : ℝ) ^ 2 := by nlinarith
          nlinarith
      _ = 2 * (H : ℝ) ^ 2 := by rw [← Finset.sum_mul, ρ.sum_prob, one_mul]
  linarith

end Analysis

end StatisticalRL.FiniteVILCB

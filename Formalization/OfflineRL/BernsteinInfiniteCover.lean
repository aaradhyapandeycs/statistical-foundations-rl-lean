import Formalization.OfflineRL.VILCBAuxiliaryAbsorbing
import Formalization.Probability.VarianceIccPerturbation
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Deterministic part of the proof of Lemma 6.6 (Steps 3–5) and the small-count case

Source: `chapters/offlineRL.tex`, proof of `lem:Bernstein-infinite` (from line 3630).

- Step 3 covering set (`eq:defn-Ucover-infinite-Bernstein`, `:3887–3937`): `uGrid`, its cover
  property `uGrid_covers`, and the cardinality bound `uGrid_card_le`. The latter needs `N ≥ 5`,
  which the printed proof assumes at line 3898 without deriving it (`docs/SOURCE-ISSUES.md#C23`).
- Repair for C23: when `N_{s,a} ≤ 26`, both conclusions hold surely (`lem66_small_count`). The
  probabilistic argument is therefore only needed for pairs with `N_{s,a} ≥ 27`, which forces
  `N ≥ 27 ≥ 5`.
- Steps 4–5 (`:3994–4273`): on the grid event of Lemma 6.18 (at log level
  `L = log(16N²/((1-γ)δ))`), the conclusions of Lemma 6.6 follow, with constants 26 and 24
  (`lem66_of_gridBound`). The fixed-grid perturbation uses the sharp `[0, C]` variance bound,
  and the perturbation to `Ṽ` (whose entries may be negative) uses the generic `4Bε` bound,
  which is at most `2C²ε` because `C = 1/(1-γ) ≥ 2`.
-/

open scoped BigOperators

namespace StatisticalRL.OfflineVILCB.Input

open StatisticalRL

variable {S A : Type*} [Fintype S] [Fintype A]

/-! ## Scalar facts -/

theorem two_le_log_eight : (2 : ℝ) ≤ Real.log 8 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h2]
  have h0 := Real.exp_pos 1
  nlinarith

/-- Bounds on `ℓ = log(4N/((1-γ)δ))` and `L = log(16N²/((1-γ)δ))`. -/
theorem logs_facts {γ δ N : ℝ} (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hN : 1 ≤ N) :
    2 ≤ Real.log (4 * N / ((1 - γ) * δ)) ∧
      Real.log (4 * N / ((1 - γ) * δ)) ≤ Real.log (16 * N ^ 2 / ((1 - γ) * δ)) ∧
      Real.log (16 * N ^ 2 / ((1 - γ) * δ)) ≤ 2 * Real.log (4 * N / ((1 - γ) * δ)) := by
  have hk : 0 < 1 - γ := by linarith
  have hkδ : 0 < (1 - γ) * δ := mul_pos hk hδ
  have hkδ1 : (1 - γ) * δ ≤ 1 / 2 := by nlinarith
  have hx : 8 ≤ 4 * N / ((1 - γ) * δ) := by
    rw [le_div_iff₀ hkδ]
    nlinarith
  refine ⟨two_le_log_eight.trans (Real.log_le_log (by norm_num) hx), ?_, ?_⟩
  · apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_right _ hkδ.le
    nlinarith
  · have hpow : 2 * Real.log (4 * N / ((1 - γ) * δ)) =
        Real.log ((4 * N / ((1 - γ) * δ)) ^ 2) := by
      rw [Real.log_pow]; norm_num
    rw [hpow]
    apply Real.log_le_log (by positivity)
    rw [div_pow, div_le_div_iff₀ hkδ (by positivity)]
    have h16 : 0 ≤ 16 * N ^ 2 := by positivity
    have : 16 * N ^ 2 * ((1 - γ) * δ) ^ 2 ≤ 16 * N ^ 2 * ((1 - γ) * δ) := by
      apply mul_le_mul_of_nonneg_left _ h16
      nlinarith
    nlinarith

/-- Scalar part of Steps 4–5 (`:4071–4273`). Here `e = 1/N`. -/
theorem steps45_scalar {C L ℓ n e D0 Dt Vh0 Vp0 Vhs Vps Vht Vpt : ℝ}
    (hC : 2 ≤ C) (hn : 0 < n) (he0 : 0 ≤ e) (he : e ≤ ℓ / n) (hℓ : 1 ≤ ℓ) (hℓL : ℓ ≤ L)
    (hL : L ≤ 2 * ℓ) (hVht : 0 ≤ Vht)
    (G1 : D0 ≤ Real.sqrt (4 * Vh0 * L / n) + 5 * L * C / n)
    (G2 : Vh0 ≤ 2 * Vp0 + 5 * L * C ^ 2 / (3 * n))
    (P1 : |Vh0 - Vhs| ≤ 2 * C ^ 2 * e) (P2 : |Vp0 - Vps| ≤ 2 * C ^ 2 * e)
    (P3 : |Vhs - Vht| ≤ 4 * C * e) (P4 : |Vps - Vpt| ≤ 4 * C * e)
    (T : Dt ≤ D0 + 2 * C * e + 2 * e) :
    Dt ≤ Real.sqrt (8 * ℓ / n * Vht) + 26 * ℓ * C / n ∧
      Vht ≤ 2 * Vpt + 24 * ℓ * C ^ 2 / n := by
  have hC0 : 0 ≤ C := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hCe : 4 * C * e ≤ 2 * C ^ 2 * e := by
    nlinarith [mul_nonneg (mul_nonneg hC0 he0) (sub_nonneg.mpr hC)]
  have h2e : 2 * e ≤ C * e := by nlinarith
  have heL : e ≤ L / n := he.trans (div_le_div_of_nonneg_right hℓL hn.le)
  obtain ⟨P1l, P1r⟩ := abs_le.mp P1
  obtain ⟨P2l, P2r⟩ := abs_le.mp P2
  obtain ⟨P3l, P3r⟩ := abs_le.mp P3
  obtain ⟨P4l, P4r⟩ := abs_le.mp P4
  -- atoms
  have hY : C * e ≤ C * ℓ / n := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left he hC0
  have hW : C ^ 2 * e ≤ C ^ 2 * ℓ / n := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left he (sq_nonneg C)
  have hX : C * L / n ≤ 2 * (C * ℓ / n) := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hn]
    nlinarith
  have hU : C ^ 2 * L / n ≤ 2 * (C ^ 2 * ℓ / n) := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hn]
    nlinarith [sq_nonneg C]
  constructor
  · have hVh0 : Vh0 ≤ Vht + 4 * C ^ 2 * e := by linarith
    have hs1 : Real.sqrt (4 * Vh0 * L / n) ≤
        Real.sqrt (4 * L * Vht / n + 16 * L * C ^ 2 * e / n) := by
      apply Real.sqrt_le_sqrt
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hn.le
      have := mul_le_mul_of_nonneg_left hVh0 (by linarith : 0 ≤ 4 * L)
      linarith
    have hs2 := sqrt_add_le_sqrt_add_sqrt
      (by positivity : 0 ≤ 4 * L * Vht / n)
      (by have := mul_nonneg (mul_nonneg hL0 (sq_nonneg C)) he0; positivity :
        0 ≤ 16 * L * C ^ 2 * e / n)
    have hs3 : Real.sqrt (4 * L * Vht / n) ≤ Real.sqrt (8 * ℓ / n * Vht) := by
      apply Real.sqrt_le_sqrt
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hn.le
      exact mul_le_mul_of_nonneg_right (by linarith) hVht
    have hs4 : Real.sqrt (16 * L * C ^ 2 * e / n) ≤ 4 * (C * L / n) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      have heq : (4 * (C * L / n)) ^ 2 = 16 * L * C ^ 2 * (L / n) / n := by
        field_simp
        ring
      rw [heq]
      apply div_le_div_of_nonneg_right _ hn.le
      exact mul_le_mul_of_nonneg_left heL (by positivity)
    have h5 : 5 * L * C / n = 5 * (C * L / n) := by ring
    rw [h5] at G1
    have h26 : 26 * ℓ * C / n = 26 * (C * ℓ / n) := by ring
    rw [h26]
    have hY0 : 0 ≤ C * ℓ / n := by positivity
    linarith only [T, G1, hs1, hs2, hs3, hs4, hX, hY, h2e, hY0]
  · have h5 : 5 * L * C ^ 2 / (3 * n) = 5 / 3 * (C ^ 2 * L / n) := by
      field_simp
    rw [h5] at G2
    have h24 : 24 * ℓ * C ^ 2 / n = 24 * (C ^ 2 * ℓ / n) := by ring
    rw [h24]
    have hR0 : 0 ≤ C ^ 2 * ℓ / n := by positivity
    linarith only [P1l, P2r, P3l, P4r, G2, hCe, hW, hU, hR0]

/-! ## The covering grid (Step 3) -/

variable (M : Input S A) [Nonempty A]

/-- `𝒰_cover = {i/N : 1 ≤ i ≤ ⌊N u_max⌋}` (`eq:defn-Ucover-infinite-Bernstein`). -/
noncomputable def uGrid (s : S) : Finset ℝ :=
  (Finset.Icc 1 ⌊(M.N : ℝ) * M.uMax s⌋₊).image fun i : ℕ => (i : ℝ) / M.N

theorem uMax_pos (s : S) : 0 < M.uMax s := by
  have h := M.five_div_le_minBonusAbs s
  have hN : (0 : ℝ) < M.N := by exact_mod_cast M.N_pos
  unfold uMax
  have : 0 ≤ 5 / (M.N : ℝ) := by positivity
  linarith

theorem le_uMax_of_mem_uGrid (s : S) {u : ℝ} (hu : u ∈ M.uGrid s) : u ≤ M.uMax s := by
  unfold uGrid at hu
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  have hN : (0 : ℝ) < M.N := by exact_mod_cast M.N_pos
  have hi2 := (Finset.mem_Icc.mp hi).2
  have hfl : (i : ℝ) ≤ M.N * M.uMax s :=
    (Nat.cast_le.mpr hi2).trans (Nat.floor_le (by have := M.uMax_pos s; positivity))
  rw [div_le_iff₀ hN]
  linarith

/-- The grid contains a point within `1/N` of every `u ∈ [5/N, u_max]` (`eq:u0-ustar-cover`). -/
theorem uGrid_covers (s : S) {u : ℝ} (hu5 : 5 / (M.N : ℝ) ≤ u) (hu : u ≤ M.uMax s) :
    ∃ u₀ ∈ M.uGrid s, |u₀ - u| ≤ 1 / M.N := by
  have hN : (0 : ℝ) < M.N := by exact_mod_cast M.N_pos
  have hNu : 5 ≤ (M.N : ℝ) * u := by
    rw [div_le_iff₀ hN] at hu5
    linarith
  set i := ⌊(M.N : ℝ) * u⌋₊ with hi
  have hi1 : 1 ≤ i := Nat.le_floor (by norm_num; linarith)
  have hiM : i ≤ ⌊(M.N : ℝ) * M.uMax s⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hu hN.le)
  refine ⟨(i : ℝ) / M.N, ?_, ?_⟩
  · unfold uGrid
    exact Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr ⟨hi1, hiM⟩, rfl⟩
  · have hle : (i : ℝ) ≤ M.N * u := Nat.floor_le (by linarith)
    have hlt : (M.N : ℝ) * u < i + 1 := Nat.lt_floor_add_one _
    have heq : (i : ℝ) / M.N - u = ((i : ℝ) - M.N * u) / M.N := by
      field_simp
    rw [heq, abs_div, abs_of_pos hN, div_le_div_iff_of_pos_right hN, abs_le]
    constructor <;> linarith

/-- `eq:defn-Ucover-infinite-Bernstein-cardinality`, under the premise `N ≥ 5` of line 3898. -/
theorem uGrid_card_le (hγ : 1 / 2 ≤ M.γ) (hN5 : 5 ≤ M.N) (s : S) :
    ((M.uGrid s).card : ℝ) ≤ 2 * M.N / (1 - M.γ) := by
  have hN : (5 : ℝ) ≤ M.N := by exact_mod_cast hN5
  have hk := M.one_sub_γ_pos
  have hC2 : 2 ≤ 1 / (1 - M.γ) := by
    rw [le_div_iff₀ hk]
    linarith
  have hcard : (M.uGrid s).card ≤ ⌊(M.N : ℝ) * M.uMax s⌋₊ := by
    unfold uGrid
    refine Finset.card_image_le.trans ?_
    simp
  have hfl : (⌊(M.N : ℝ) * M.uMax s⌋₊ : ℝ) ≤ M.N * M.uMax s :=
    Nat.floor_le (by have := M.uMax_pos s; positivity)
  have hum : M.uMax s ≤ 1 / (1 - M.γ) + 5 / M.N + 1 := by
    have := M.minBonusAbs_le_bound s
    unfold uMax
    linarith
  have hNu : (M.N : ℝ) * M.uMax s ≤ M.N * (1 / (1 - M.γ)) + 5 + M.N := by
    have h := mul_le_mul_of_nonneg_left hum (by linarith : (0 : ℝ) ≤ M.N)
    have h5 : (M.N : ℝ) * (5 / M.N) = 5 := by field_simp
    nlinarith
  have hfinal : (M.N : ℝ) * (1 / (1 - M.γ)) + 5 + M.N ≤ 2 * M.N / (1 - M.γ) := by
    have h1 : 2 * (M.N : ℝ) / (1 - M.γ) = 2 * (M.N * (1 / (1 - M.γ))) := by ring
    rw [h1]
    nlinarith
  calc ((M.uGrid s).card : ℝ) ≤ (⌊(M.N : ℝ) * M.uMax s⌋₊ : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := hfl.trans (hNu.trans hfinal)

/-! ## The grid event and the deterministic conclusion -/

/-- The two Lemma 6.18 inequalities for the row `(s,a)`, the true row `d` and a vector `V`, at the
log level `L` (Lemma 6.18 with `log(1/δ) = L`). -/
def GridBound (d : FiniteDistribution S) (s : S) (a : A) (L : ℝ) (V : S → ℝ) : Prop :=
  |(M.Phat s a).expectation V - d.expectation V| ≤
      Real.sqrt (4 * (M.Phat s a).variance V * L / M.count s a) +
        5 * L / ((1 - M.γ) * M.count s a) ∧
    (M.Phat s a).variance V ≤ 2 * d.variance V + 5 * L / (3 * (1 - M.γ) ^ 2 * M.count s a)

/-- The two printed conclusions of Lemma 6.6 for the row `(s,a)` and the vector `Vt`. -/
def Lemma66Bound (d : FiniteDistribution S) (s : S) (a : A) (ℓ : ℝ) (Vt : S → ℝ) : Prop :=
  |(M.Phat s a).expectation Vt - d.expectation Vt| ≤
      Real.sqrt (8 * ℓ / M.count s a * (M.Phat s a).variance Vt) +
        26 * ℓ / ((1 - M.γ) * M.count s a) ∧
    (M.Phat s a).variance Vt ≤ 2 * d.variance Vt + 24 * ℓ / ((1 - M.γ) ^ 2 * M.count s a)

omit [Nonempty A] in
/-- C23 repair: for `1 ≤ N_{s,a} ≤ 26` both conclusions hold surely, for every `Ṽ` with
`‖Ṽ‖∞ ≤ 1/(1-γ)`, as soon as `ℓ ≥ 2`. -/
theorem lem66_small_count (d : FiniteDistribution S) (s : S) (a : A) {ℓ : ℝ} (hℓ : 2 ≤ ℓ)
    (hpos : 0 < M.count s a) (hsmall : M.count s a ≤ 26) (Vt : S → ℝ)
    (hbd : ∀ t, |Vt t| ≤ 1 / (1 - M.γ)) : M.Lemma66Bound d s a ℓ Vt := by
  have hk := M.one_sub_γ_pos
  set C := 1 / (1 - M.γ) with hCdef
  have hC : 0 < C := by positivity
  have hn : (0 : ℝ) < M.count s a := by exact_mod_cast hpos
  have hn26 : (M.count s a : ℝ) ≤ 26 := by exact_mod_cast hsmall
  have hdev : |(M.Phat s a).expectation Vt - d.expectation Vt| ≤ 2 * C := by
    have h1 := (M.Phat s a).abs_expectation_le hbd
    have h2 := d.abs_expectation_le hbd
    calc _ ≤ |(M.Phat s a).expectation Vt| + |d.expectation Vt| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  have hvar : (M.Phat s a).variance Vt ≤ C ^ 2 := by
    refine ((M.Phat s a).variance_le_expectation_sq Vt).trans
      ((M.Phat s a).expectation_le_const fun t => ?_)
    have := hbd t
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have e1 : 26 * ℓ / ((1 - M.γ) * M.count s a) = 26 * ℓ * C / M.count s a := by
    rw [hCdef]; field_simp
  have e2 : 24 * ℓ / ((1 - M.γ) ^ 2 * M.count s a) = 24 * ℓ * C ^ 2 / M.count s a := by
    rw [hCdef]; field_simp
  unfold Lemma66Bound
  rw [e1, e2]
  constructor
  · have : 2 * C ≤ 26 * ℓ * C / M.count s a := by
      rw [le_div_iff₀ hn]
      nlinarith
    linarith [Real.sqrt_nonneg (8 * ℓ / M.count s a * (M.Phat s a).variance Vt)]
  · have : C ^ 2 ≤ 24 * ℓ * C ^ 2 / M.count s a := by
      rw [le_div_iff₀ hn]
      nlinarith [sq_nonneg C, mul_pos hC hC]
    linarith [d.variance_nonneg Vt]

/-- Steps 4–5 (`:3994–4273`): on the grid event at level `L = log(16N²/((1-γ)δ))`, the two
conclusions of Lemma 6.6 hold at level `ℓ = log(4N/((1-γ)δ))` for every `Ṽ` with
`‖Ṽ − V̂⋆_pe‖∞ ≤ 1/N` and `‖Ṽ‖∞ ≤ 1/(1-γ)`. -/
theorem lem66_of_gridBound (hγ : 1 / 2 ≤ M.γ) (d : FiniteDistribution S) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) (Qstar : S → A → ℝ) (hfix : M.pess Qstar = Qstar) (s : S) (a : A)
    (hpos : 0 < M.count s a) (hcN : M.count s a ≤ M.N)
    (hgrid : ∀ u ∈ M.uGrid s,
      M.GridBound d s a (Real.log (16 * (M.N : ℝ) ^ 2 / ((1 - M.γ) * δ))) (value (M.auxFix s u)))
    (Vt : S → ℝ) (hclose : ∀ t, |Vt t - value Qstar t| ≤ 1 / M.N)
    (hbd : ∀ t, |Vt t| ≤ 1 / (1 - M.γ)) :
    M.Lemma66Bound d s a (Real.log (4 * (M.N : ℝ) / ((1 - M.γ) * δ))) Vt := by
  have hk := M.one_sub_γ_pos
  have hNpos : (0 : ℝ) < M.N := by exact_mod_cast M.N_pos
  have hN1 : (1 : ℝ) ≤ M.N := by exact_mod_cast M.N_pos
  have hn : (0 : ℝ) < M.count s a := by exact_mod_cast hpos
  have hnN : (M.count s a : ℝ) ≤ M.N := by exact_mod_cast hcN
  set C := 1 / (1 - M.γ) with hCdef
  have hC2 : 2 ≤ C := by
    rw [hCdef, le_div_iff₀ hk]
    linarith
  set L := Real.log (16 * (M.N : ℝ) ^ 2 / ((1 - M.γ) * δ)) with hLdef
  set ℓ := Real.log (4 * (M.N : ℝ) / ((1 - M.γ) * δ)) with hℓdef
  obtain ⟨hℓ2, hℓL, hL2⟩ := logs_facts hγ M.γ_lt_one hδ hδ1 hN1
  set n : ℝ := (M.count s a : ℝ) with hndef
  set e : ℝ := 1 / M.N with hedef
  have he0 : 0 ≤ e := by positivity
  have he : e ≤ ℓ / n := by
    rw [hedef, div_le_div_iff₀ hNpos hn]
    nlinarith
  -- the grid point near u⋆
  have hbox := M.fixed_mem_box Qstar hfix
  obtain ⟨u₀, hu₀, hcl⟩ := M.uGrid_covers s (M.five_div_le_ustar Qstar hbox s)
    (M.ustar_le_uMax Qstar hbox s)
  have hu₀le := M.le_uMax_of_mem_uGrid s hu₀
  have husle := M.ustar_le_uMax Qstar hbox s
  set V0 := value (M.auxFix s u₀) with hV0def
  set Vs := value Qstar with hVsdef
  have hVsfix : value (M.auxFix s (M.ustar Qstar s)) = Vs := M.value_auxFix_ustar hγ Qstar hfix s
  have hV0r := M.value_auxFix_mem hγ s hu₀le
  have hVsr : ∀ t, 0 ≤ Vs t ∧ Vs t ≤ C := fun t =>
    ⟨M.value_nonneg Qstar hbox t, M.value_le_bound Qstar hbox t⟩
  have hgap : ∀ t, |V0 t - Vs t| ≤ C * e := by
    intro t
    have h := M.value_auxFix_lipschitz hγ s hu₀le husle t
    rw [hVsfix] at h
    refine h.trans ?_
    have h1 : |u₀ - M.ustar Qstar s| / (1 - M.γ) ≤ (1 / M.N) / (1 - M.γ) :=
      div_le_div_of_nonneg_right hcl hk.le
    refine h1.trans (le_of_eq ?_)
    rw [hCdef, hedef]
    ring
  obtain ⟨G1, G2⟩ := hgrid u₀ hu₀
  -- variance perturbations
  have hV0I : ∀ t, V0 t ∈ Set.Icc 0 C := fun t => ⟨(hV0r t).1, (hV0r t).2⟩
  have hVsI : ∀ t, Vs t ∈ Set.Icc 0 C := fun t => ⟨(hVsr t).1, (hVsr t).2⟩
  have P1 : |(M.Phat s a).variance V0 - (M.Phat s a).variance Vs| ≤ 2 * C ^ 2 * e := by
    have h := (M.Phat s a).abs_variance_sub_le_of_Icc hV0I hVsI hgap
    calc _ ≤ 2 * C * (C * e) := h
      _ = 2 * C ^ 2 * e := by ring
  have P2 : |d.variance V0 - d.variance Vs| ≤ 2 * C ^ 2 * e := by
    have h := d.abs_variance_sub_le_of_Icc hV0I hVsI hgap
    calc _ ≤ 2 * C * (C * e) := h
      _ = 2 * C ^ 2 * e := by ring
  have hVsabs : ∀ t, |Vs t| ≤ C := fun t => by
    rw [abs_of_nonneg (hVsr t).1]; exact (hVsr t).2
  have hclose' : ∀ t, |Vs t - Vt t| ≤ e := fun t => by
    rw [abs_sub_comm]; exact hclose t
  have P3 : |(M.Phat s a).variance Vs - (M.Phat s a).variance Vt| ≤ 4 * C * e :=
    (M.Phat s a).abs_variance_sub_le he0 hVsabs hbd hclose'
  have P4 : |d.variance Vs - d.variance Vt| ≤ 4 * C * e :=
    d.abs_variance_sub_le he0 hVsabs hbd hclose'
  -- triangle step
  have T : |(M.Phat s a).expectation Vt - d.expectation Vt| ≤
      |(M.Phat s a).expectation V0 - d.expectation V0| + 2 * C * e + 2 * e := by
    have h1 := (M.Phat s a).abs_expectation_sub_le (f := Vs) (g := V0)
      fun t => by rw [abs_sub_comm]; exact hgap t
    have h2 := d.abs_expectation_sub_le (f := Vs) (g := V0)
      fun t => by rw [abs_sub_comm]; exact hgap t
    have h3 := (M.Phat s a).abs_expectation_sub_le (f := Vt) (g := Vs) hclose
    have h4 := d.abs_expectation_sub_le (f := Vt) (g := Vs) hclose
    have h0 := le_abs_self ((M.Phat s a).expectation V0 - d.expectation V0)
    have h0' := neg_abs_le ((M.Phat s a).expectation V0 - d.expectation V0)
    rw [abs_le] at h1 h2 h3 h4 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  -- rewrite the grid inequalities with `C`
  have g1 : 5 * L / ((1 - M.γ) * n) = 5 * L * C / n := by rw [hCdef]; field_simp
  have g2 : 5 * L / (3 * (1 - M.γ) ^ 2 * n) = 5 * L * C ^ 2 / (3 * n) := by
    rw [hCdef]; field_simp
  rw [g1] at G1
  rw [g2] at G2
  have G1' : |(M.Phat s a).expectation V0 - d.expectation V0| ≤
      Real.sqrt (4 * (M.Phat s a).variance V0 * L / n) + 5 * L * C / n := G1
  have hres := steps45_scalar hC2 hn he0 he (by linarith) hℓL hL2
    ((M.Phat s a).variance_nonneg Vt) G1' G2 P1 P2 P3 P4 T
  have e1 : 26 * ℓ / ((1 - M.γ) * n) = 26 * ℓ * C / n := by rw [hCdef]; field_simp
  have e2 : 24 * ℓ / ((1 - M.γ) ^ 2 * n) = 24 * ℓ * C ^ 2 / n := by rw [hCdef]; field_simp
  unfold Lemma66Bound
  rw [e1, e2]
  exact hres

/-- Lemma 6.6 for one row, deterministically from the grid event, including the C23 case split:
the grid event is only needed when `N_{s,a} ≥ 27`. -/
theorem lem66_of_gridBound_or_small (hγ : 1 / 2 ≤ M.γ) (d : FiniteDistribution S) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (Qstar : S → A → ℝ) (hfix : M.pess Qstar = Qstar) (s : S) (a : A)
    (hpos : 0 < M.count s a) (hcN : M.count s a ≤ M.N)
    (hgrid : 27 ≤ M.count s a → ∀ u ∈ M.uGrid s,
      M.GridBound d s a (Real.log (16 * (M.N : ℝ) ^ 2 / ((1 - M.γ) * δ))) (value (M.auxFix s u)))
    (Vt : S → ℝ) (hclose : ∀ t, |Vt t - value Qstar t| ≤ 1 / M.N)
    (hbd : ∀ t, |Vt t| ≤ 1 / (1 - M.γ)) :
    M.Lemma66Bound d s a (Real.log (4 * (M.N : ℝ) / ((1 - M.γ) * δ))) Vt := by
  by_cases h27 : 27 ≤ M.count s a
  · exact M.lem66_of_gridBound hγ d hδ hδ1 Qstar hfix s a hpos hcN (hgrid h27) Vt hclose hbd
  · have hN1 : (1 : ℝ) ≤ M.N := by exact_mod_cast M.N_pos
    exact M.lem66_small_count d s a (logs_facts hγ M.γ_lt_one hδ hδ1 hN1).1 hpos
      (by omega) Vt hbd

end StatisticalRL.OfflineVILCB.Input

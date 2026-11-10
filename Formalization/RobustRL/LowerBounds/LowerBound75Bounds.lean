import Formalization.RobustRL.LowerBounds.LowerBound75Params
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Corrected Theorem 7.5: constant tracking

Constants: `c₃ = 1/512` (so `128 h ε ≤ 1/4`), `c₄ = 1/5308416 = 1/(324 · 128²)`.
-/

namespace StatisticalRL.RobustRL.Ch7.LowerBound75

variable {s u h ε : ℝ}

section

variable (hs0 : 0 ≤ s) (hu : 0 < u) (hsu : s ≤ u) (hd : u ^ 2 = s * u + h) (hh0 : 0 < h)
  (hh1 : h ≤ 1 / 4) (hε : 0 < ε) (hhε : h * ε ≤ 1 / 512)

include hs0 hu hsu hd hh0 hh1 hε hhε

omit hd hh1 hhε in
theorem df_pos : 0 < df s u h ε := by
  unfold df; have := pf_pos hs0 hu hsu; positivity

/-- (A5) `δ ≤ u`. -/
theorem df_le : df s u h ε ≤ u := by
  have hP := pf_pos hs0 hu hsu
  unfold df
  rw [div_le_iff₀ hP]
  have k := key_delta hd hh0 hh1
  have e : 128 * h ^ 2 * ε * (1 + u ^ 2) ^ 2 = (128 * (h * ε)) * (h * (1 + u ^ 2) ^ 2) := by ring
  rw [e]
  have a : 128 * (h * ε) ≤ 1 / 4 := by linarith
  have b : 0 ≤ h * (1 + u ^ 2) ^ 2 := by positivity
  have c : 0 ≤ 128 * (h * ε) := by positivity
  nlinarith

omit hd hh1 hhε in
theorem df_mul_pf : df s u h ε * pf s u = 128 * h ^ 2 * ε * (1 + u ^ 2) ^ 2 := by
  have hP := pf_pos hs0 hu hsu
  unfold df; field_simp

/-- `1 + u'² ≤ 4 (1 + u²)` and `1 + u² ≤ 1 + u'²`. -/
theorem den_bounds :
    1 + u ^ 2 ≤ 1 + (u + df s u h ε) ^ 2 ∧ 1 + (u + df s u h ε) ^ 2 ≤ 4 * (1 + u ^ 2) := by
  have hδ := df_pos hs0 hu hsu hh0 hε
  have hδu := df_le hs0 hu hsu hd hh0 hh1 hε hhε
  constructor <;> nlinarith

/-- (b) `T(u') - T(u) ≥ 32 h² ε`. -/
theorem tdiff_lower : 32 * h ^ 2 * ε ≤ tf s (u + df s u h ε) - tf s u := by
  have hδ := df_pos hs0 hu hsu hh0 hε
  have hP := pf_pos hs0 hu hsu
  obtain ⟨d1, d2⟩ := den_bounds hs0 hu hsu hd hh0 hh1 hε hhε
  rw [tf_diff]
  set δ := df s u h ε
  have hA : 0 < 1 + u ^ 2 := by positivity
  have hB : 0 < 1 + (u + δ) ^ 2 := by positivity
  rw [le_div_iff₀ (mul_pos hA hB)]
  have hm := df_mul_pf hs0 hu hsu hh0 hε
  have hsu0 : 0 ≤ δ * (δ * (1 + s * u)) := by positivity
  have e : δ * (pf s u + δ * (1 + s * u)) = δ * pf s u + δ * (δ * (1 + s * u)) := by ring
  rw [e, hm]
  have : (1 + u ^ 2) * (1 + (u + δ) ^ 2) ≤ (1 + u ^ 2) * (4 * (1 + u ^ 2)) :=
    mul_le_mul_of_nonneg_left d2 hA.le
  have hc : 0 ≤ 32 * h ^ 2 * ε := by positivity
  nlinarith

/-- (c) `T(u') ≤ 3h/2`. -/
theorem tg_le : tf s (u + df s u h ε) ≤ 3 / 2 * h := by
  have hδ := df_pos hs0 hu hsu hh0 hε
  have hδu := df_le hs0 hu hsu hd hh0 hh1 hε hhε
  have hP := pf_pos hs0 hu hsu
  obtain ⟨d1, d2⟩ := den_bounds hs0 hu hsu hd hh0 hh1 hε hhε
  have hdiff := tf_diff (s := s) (u := u) (df s u h ε)
  have hbase := tf_base hd
  set δ := df s u h ε
  have hA : 0 < 1 + u ^ 2 := by positivity
  have hB : 0 < 1 + (u + δ) ^ 2 := by positivity
  have hm := df_mul_pf hs0 hu hsu hh0 hε
  -- `E ≤ 2P`
  have hE : pf s u + δ * (1 + s * u) ≤ 2 * pf s u := by
    have : δ * (1 + s * u) ≤ u * (1 + s * u) :=
      mul_le_mul_of_nonneg_right hδu (by positivity)
    unfold pf at *
    nlinarith
  have hup : tf s (u + δ) - tf s u ≤ 256 * h ^ 2 * ε := by
    rw [hdiff, div_le_iff₀ (mul_pos hA hB)]
    have h1 : δ * (pf s u + δ * (1 + s * u)) ≤ δ * (2 * pf s u) :=
      mul_le_mul_of_nonneg_left hE hδ.le
    have h2 : (1 + u ^ 2) * (1 + u ^ 2) ≤ (1 + u ^ 2) * (1 + (u + δ) ^ 2) :=
      mul_le_mul_of_nonneg_left d1 hA.le
    have hc : 0 ≤ 256 * h ^ 2 * ε := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 hc
    nlinarith
  have hb : tf s u ≤ h := by
    rw [hbase, div_le_iff₀ hA]; nlinarith [sq_nonneg u]
  have : 256 * h ^ 2 * ε ≤ h / 2 := by nlinarith
  linarith

omit hs0 hsu hh1 hε hhε in
theorem tb_nonneg : 0 ≤ tf s u := by
  rw [tf_base hd]; positivity

/-- (e) the test budget: `2N KL-proxy ≤ log 2` under `N h⁴ ε² ≤ c₄ (h + s²)`. -/
theorem test_budget {N : ℝ} (hN0 : 0 ≤ N)
    (hN : N * (h ^ 4 * ε ^ 2) ≤ 1 / 5308416 * (h + s ^ 2)) :
    2 * N * ((ellf (u + df s u h ε) - ellf u) ^ 2 / (ellf u * (1 - ellf u))) ≤
      Real.log 2 := by
  have hδ := df_pos hs0 hu hsu hh0 hε
  have hδu := df_le hs0 hu hsu hd hh0 hh1 hε hhε
  have hP := pf_pos hs0 hu hsu
  obtain ⟨d1, d2⟩ := den_bounds hs0 hu hsu hd hh0 hh1 hε hhε
  have hm := df_mul_pf hs0 hu hsu hh0 hε
  have kt := key_test hu hd hh0 hh1
  rw [ellf_diff, ellf_var]
  set δ := df s u h ε
  set A := 1 + u ^ 2 with hAdef
  set B := 1 + (u + δ) ^ 2 with hBdef
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hu2 : 0 < u ^ 2 := by positivity
  -- ratio ≤ 9 δ² / A²
  have hratio : (δ * (2 * u + δ) / (A * B)) ^ 2 / (u ^ 2 / A ^ 2) ≤ 9 * δ ^ 2 / A ^ 2 := by
    have e : (δ * (2 * u + δ) / (A * B)) ^ 2 / (u ^ 2 / A ^ 2) =
        δ ^ 2 * (2 * u + δ) ^ 2 / (u ^ 2 * B ^ 2) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (2 * u + δ) ^ 2 ≤ 9 * u ^ 2 := by nlinarith
    have h2 : A ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hA.le d1 2
    have h3 : δ ^ 2 * (2 * u + δ) ^ 2 * A ^ 2 ≤ δ ^ 2 * (9 * u ^ 2) * A ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (sq_nonneg δ)
      exact mul_le_mul_of_nonneg_right this (sq_nonneg A)
    have h4 : δ ^ 2 * (9 * u ^ 2) * A ^ 2 ≤ δ ^ 2 * (9 * u ^ 2) * B ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith
  -- `δ² / A² = 128² h⁴ ε² A² / P²`
  have hδA : δ ^ 2 / A ^ 2 = 128 ^ 2 * (h ^ 4 * ε ^ 2) * A ^ 2 / pf s u ^ 2 := by
    have : δ = 128 * h ^ 2 * ε * A ^ 2 / pf s u := rfl
    rw [this]; field_simp
  have hlog : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hmain : 2 * N * (9 * δ ^ 2 / A ^ 2) ≤ 1 / 2 := by
    have e : 2 * N * (9 * δ ^ 2 / A ^ 2) = 18 * 128 ^ 2 * (N * (h ^ 4 * ε ^ 2)) * A ^ 2 /
        pf s u ^ 2 := by
      rw [mul_div_assoc, hδA]; ring
    rw [e, div_le_iff₀ (by positivity)]
    have h1 : 18 * 128 ^ 2 * (N * (h ^ 4 * ε ^ 2)) * A ^ 2 ≤
        18 * 128 ^ 2 * (1 / 5308416 * (h + s ^ 2)) * A ^ 2 := by
      have := mul_le_mul_of_nonneg_left hN (by norm_num : (0 : ℝ) ≤ 18 * 128 ^ 2)
      exact mul_le_mul_of_nonneg_right this (sq_nonneg A)
    have h2 : (h + s ^ 2) * A ^ 2 ≤ 9 * pf s u ^ 2 := kt
    nlinarith
  have := mul_le_mul_of_nonneg_left hratio (by positivity : (0 : ℝ) ≤ 2 * N)
  linarith

end

/-- `ychi γ a - ychi γ b = γ (a - b) / ((1-γ+γa)(1-γ+γb))`. -/
theorem ychi_sub {γ a b : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ychi γ a - ychi γ b = γ * (a - b) / ((1 - γ + γ * a) * (1 - γ + γ * b)) := by
  have h1 : (1 - γ) ≠ 0 := by linarith
  have h2 : (1 - γ + γ * a) ≠ 0 := by have := mul_nonneg hγ0 ha; linarith
  have h3 : (1 - γ + γ * b) ≠ 0 := by have := mul_nonneg hγ0 hb; linarith
  unfold ychi
  field_simp
  ring

/-- (F7) Gap: if `0 ≤ b ≤ a - D/2`, `D ≥ 32 h² ε`, `a ≤ 3h/2`, `γ ≥ 3/4`, then
`ychi a - ychi b ≥ (48/25) ε > ε`. -/
theorem chi_gap_gt {γ ε a b D : ℝ} (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε) (hb : 0 ≤ b)
    (hab : b ≤ a - D / 2) (hD : 32 * (1 - γ) ^ 2 * ε ≤ D) (ha : a ≤ 3 / 2 * (1 - γ)) :
    ε < ychi γ a - ychi γ b := by
  have hγ0 : 0 ≤ γ := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have ha0 : 0 ≤ a := by linarith
  rw [ychi_sub hγ0 hγ1 ha0 hb]
  have hX : 0 < 1 - γ + γ * a := by have := mul_nonneg hγ0 ha0; linarith
  have hY : 0 < 1 - γ + γ * b := by have := mul_nonneg hγ0 hb; linarith
  rw [lt_div_iff₀ (mul_pos hX hY)]
  have hXle : 1 - γ + γ * a ≤ 5 / 2 * (1 - γ) := by nlinarith
  have hYle : 1 - γ + γ * b ≤ 5 / 2 * (1 - γ) := by nlinarith
  have hXY : (1 - γ + γ * a) * (1 - γ + γ * b) ≤ 25 / 4 * (1 - γ) ^ 2 := by
    have := mul_le_mul hXle hYle hY.le (by positivity)
    nlinarith
  have hnum : 12 * (1 - γ) ^ 2 * ε ≤ γ * (a - b) := by
    have : 16 * (1 - γ) ^ 2 * ε ≤ a - b := by linarith
    have h2 := mul_le_mul hγ this (by positivity) hγ0
    nlinarith
  have hpos : 0 < (1 - γ) ^ 2 * ε := by positivity
  nlinarith

end StatisticalRL.RobustRL.Ch7.LowerBound75

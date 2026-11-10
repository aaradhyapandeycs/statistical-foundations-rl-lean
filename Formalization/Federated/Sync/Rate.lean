import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Corrected Theorem 7.9 (FedSynQ): rate arithmetic

Constants `c_η = 1/216`, `c_T = 10⁴`. Notation: `g = 1-γ ∈ (0,1]`, `P = SAKT`,
`ℓ = log(P/δ)`, `η = c_η K g⁴ ε² / ℓ`, `ℓ_T = log(P/(δ ε g²))`; the `T` condition is
`c_T/(K g⁵ ε²) · ℓ_T³ ≤ T`. Every `T` above the minimum is covered (the hypotheses are lower
bounds on `T`).

* `noise_le` (`P ≥ 2`): `σ ≤ gε/2` for `σ = √(2 (1/g)² (2η/K) log(2C/δ))` whenever `1 ≤ C`
  and `2C ≤ 4P` (`C = (T+1)KSA`).
* `bias_le` (`P ≥ 2`): `(1-ηg)^T / g ≤ ε/2`.
* `degenerate_le` (`P = 1`): `(1-ηg)/g ≤ ε`.
All constant inequalities are proved with explicit numerals.
-/

namespace StatisticalRL.Ch7Rest.FedSync

/-- `log 2 > 0.69` packaged. -/
theorem log_two_gt : (0.69 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

theorem noise_le (g ε δ η Kr P C : ℝ) (hg0 : 0 < g) (hε0 : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hK : 0 < Kr) (hP2 : 2 ≤ P) (hC : 1 ≤ C) (hCP : 2 * C ≤ 4 * P)
    (hη : η = 1 / 216 * Kr * g ^ 4 * ε ^ 2 / Real.log (P / δ)) :
    Real.sqrt (2 * ((1 / g) ^ 2 * (2 * η / Kr)) * Real.log (2 / (δ / C))) ≤ g * ε / 2 := by
  have hPδ : 2 ≤ P / δ := by
    rw [le_div_iff₀ hδ0]; nlinarith
  have hℓ : Real.log 2 ≤ Real.log (P / δ) := Real.log_le_log (by norm_num) hPδ
  have hl2 := log_two_gt
  have hℓpos : 0 < Real.log (P / δ) := by linarith
  set ℓ := Real.log (P / δ) with hℓdef
  set L := Real.log (2 / (δ / C)) with hLdef
  have hL0 : 0 ≤ L := by
    apply Real.log_nonneg
    rw [div_div_eq_mul_div, le_div_iff₀ hδ0]
    linarith
  have hL : L ≤ 3 * ℓ := by
    have h1 : 2 / (δ / C) ≤ 4 * (P / δ) := by
      rw [div_div_eq_mul_div, mul_div_assoc', div_le_div_iff_of_pos_right hδ0]
      linarith
    have h2 : L ≤ Real.log (4 * (P / δ)) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (by positivity)] at h2
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hX : 2 * ((1 / g) ^ 2 * (2 * η / Kr)) * L = g ^ 2 * ε ^ 2 * L / (54 * ℓ) := by
    rw [hη]
    field_simp
    ring
  rw [hX]
  have hge : 0 ≤ g * ε / 2 := by positivity
  rw [← Real.sqrt_sq hge]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ (by positivity)]
  have hgε : 0 ≤ g ^ 2 * ε ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hL hgε
  nlinarith

theorem bias_le (g ε δ η Kr P : ℝ) (T : ℕ) (hg0 : 0 < g) (hg1 : g ≤ 1) (hε0 : 0 < ε)
    (hεg : ε * g ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hK : 0 < Kr) (hP2 : 2 ≤ P)
    (hη : η = 1 / 216 * Kr * g ^ 4 * ε ^ 2 / Real.log (P / δ)) (hη1 : η ≤ 1)
    (hTc : 10000 / (Kr * g ^ 5 * ε ^ 2) * Real.log (P / (δ * ε * g ^ 2)) ^ 3 ≤ T) :
    (1 - η * g) ^ T * (1 / g) ≤ ε / 2 := by
  have hPδ : 2 ≤ P / δ := by
    rw [le_div_iff₀ hδ0]; nlinarith
  have hl2 := log_two_gt
  have hℓ : Real.log 2 ≤ Real.log (P / δ) := Real.log_le_log (by norm_num) hPδ
  have hℓpos : 0 < Real.log (P / δ) := by linarith
  set ℓ := Real.log (P / δ) with hℓdef
  set ℓT := Real.log (P / (δ * ε * g ^ 2)) with hℓTdef
  have hεg2 : ε * g ^ 2 ≤ 1 := by
    calc ε * g ^ 2 = (ε * g) * g := by ring
      _ ≤ 1 * 1 := mul_le_mul hεg hg1 hg0.le (by norm_num)
      _ = 1 := by norm_num
  have hℓT : ℓ ≤ ℓT := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hδ0 (by positivity)]
    have : δ * ε * g ^ 2 ≤ δ := by
      calc δ * ε * g ^ 2 = δ * (ε * g ^ 2) := by ring
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hεg2 hδ0.le
        _ = δ := mul_one δ
    nlinarith
  have hℓT2 : Real.log (2 / (ε * g)) ≤ ℓT := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 2 * δ * g ≤ P := by nlinarith
    have h2 : 0 < ε * g := by positivity
    nlinarith
  have hℓTpos : 0 < ℓT := lt_of_lt_of_le hℓpos hℓT
  set Y := Kr * g ^ 5 * ε ^ 2 with hY
  have hYpos : 0 < Y := by positivity
  have hTY : 10000 * ℓT ^ 3 ≤ T * Y := by
    have := hTc
    rw [div_mul_eq_mul_div, div_le_iff₀ hYpos] at this
    linarith
  have hηgT : η * g * T = T * Y / (216 * ℓ) := by
    rw [hη, hY]
    field_simp
  -- key: ℓT ≤ η g T
  have hkey : ℓT ≤ η * g * T := by
    rw [hηgT, le_div_iff₀ (by positivity)]
    have h1 : ℓT * ℓT * ℓ ≤ ℓT ^ 3 := by
      have := mul_le_mul_of_nonneg_left hℓT (by positivity : 0 ≤ ℓT * ℓT)
      nlinarith
    have h2 : 216 * (ℓT * ℓ) ≤ 10000 * (ℓT * ℓT * ℓ) := by
      have hlt : (0.69 : ℝ) ≤ ℓT := by linarith
      have hp : 0 ≤ ℓT * ℓ := by positivity
      have := mul_le_mul_of_nonneg_left hlt hp
      nlinarith
    nlinarith
  have hηg0 : 0 ≤ η * g := by
    have : 0 ≤ η := by rw [hη]; positivity
    positivity
  have hρ0 : 0 ≤ 1 - η * g := by
    have : η * g ≤ 1 := by
      calc η * g ≤ 1 * 1 := mul_le_mul hη1 hg1 hg0.le (by norm_num)
        _ = 1 := by norm_num
    linarith
  have hexp : (1 - η * g) ^ T ≤ ε * g / 2 := by
    calc (1 - η * g) ^ T ≤ Real.exp (-(η * g)) ^ T := by
          apply pow_le_pow_left₀ hρ0
          have := Real.add_one_le_exp (-(η * g))
          linarith
      _ = Real.exp (-(η * g * T)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
      _ ≤ Real.exp (-Real.log (2 / (ε * g))) := by
          apply Real.exp_le_exp.mpr
          linarith
      _ = ε * g / 2 := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          field_simp
  calc (1 - η * g) ^ T * (1 / g) ≤ ε * g / 2 * (1 / g) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = ε / 2 := by field_simp

theorem degenerate_le (g ε δ η : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1) (hε0 : 0 < ε)
    (hεg : ε * g ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hη : η = 1 / 216 * g ^ 4 * ε ^ 2 / Real.log (1 / δ))
    (hTc : 10000 / (g ^ 5 * ε ^ 2) * Real.log (1 / (δ * ε * g ^ 2)) ^ 3 ≤ 1) :
    (1 - η * g) * (1 / g) ≤ ε := by
  have hεg2 : ε * g ^ 2 ≤ 1 := by
    calc ε * g ^ 2 = (ε * g) * g := by ring
      _ ≤ 1 * 1 := mul_le_mul hεg hg1 hg0.le (by norm_num)
      _ = 1 := by norm_num
  have hD0 : 0 < δ * ε * g ^ 2 := by positivity
  have hD1 : δ * ε * g ^ 2 ≤ 1 := by
    calc δ * ε * g ^ 2 = δ * (ε * g ^ 2) := by ring
      _ ≤ 1 * 1 := mul_le_mul hδ1.le hεg2 (by positivity) (by norm_num)
      _ = 1 := by norm_num
  set ℓT := Real.log (1 / (δ * ε * g ^ 2)) with hℓTdef
  have hℓT0 : 0 ≤ ℓT := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hD0]; linarith
  -- ℓT ≤ 1/20
  have hg5 : g ^ 5 * ε ^ 2 ≤ 1 := by
    have h1 : g ^ 5 * ε ^ 2 = g ^ 3 * (ε * g) ^ 2 := by ring
    have h2 : g ^ 3 ≤ 1 := pow_le_one₀ hg0.le hg1
    have h3 : (ε * g) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hεg
    rw [h1]
    calc g ^ 3 * (ε * g) ^ 2 ≤ 1 * 1 := mul_le_mul h2 h3 (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hcube : 10000 * ℓT ^ 3 ≤ 1 := by
    have hpos : 0 < g ^ 5 * ε ^ 2 := by positivity
    have := hTc
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos] at this
    linarith
  have hsmall : ℓT ≤ 1 / 20 := by
    by_contra hcon
    push_neg at hcon
    have : (1 / 20 : ℝ) ^ 3 < ℓT ^ 3 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
    norm_num at this
    linarith
  -- component bounds
  have hlx : Real.log (1 / (ε * g)) ≤ ℓT := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by positivity) hD0]
    have : δ * g ≤ 1 := by nlinarith
    nlinarith [mul_pos hε0 hg0]
  have hlg : Real.log (1 / g) ≤ ℓT := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hg0 hD0]
    have : δ * (ε * g) ≤ 1 := by nlinarith
    nlinarith
  have hlδ : Real.log (1 / δ) ≤ ℓT := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hδ0 hD0]
    nlinarith
  have hℓpos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ0]; linarith
  have hmono : ∀ y : ℝ, 0 < y → 1 - y ≤ Real.log (1 / y) := by
    intro y hy
    rw [one_div, Real.log_inv]
    have := Real.log_le_sub_one_of_pos hy
    linarith
  have hx : 19 / 20 ≤ ε * g := by
    have := hmono (ε * g) (by positivity)
    linarith
  have hgl : 19 / 20 ≤ g := by
    have := hmono g hg0
    linarith
  have hprod : 3 / 4 ≤ g ^ 3 * (ε * g) ^ 2 := by
    have h1 : (19 / 20 : ℝ) ^ 3 ≤ g ^ 3 := pow_le_pow_left₀ (by norm_num) hgl 3
    have h2 : (19 / 20 : ℝ) ^ 2 ≤ (ε * g) ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
    have h3 : (19 / 20 : ℝ) ^ 3 * (19 / 20) ^ 2 ≤ g ^ 3 * (ε * g) ^ 2 :=
      mul_le_mul h1 h2 (by norm_num) (by positivity)
    norm_num at h3
    linarith
  set ℓ := Real.log (1 / δ) with hℓdef
  have hηg : η * g = g ^ 3 * (ε * g) ^ 2 / (216 * ℓ) := by
    rw [hη]
    field_simp
  have hkey : 1 - ε * g ≤ η * g := by
    rw [hηg, le_div_iff₀ (by positivity)]
    have h1 : 1 - ε * g ≤ ℓT := le_trans (hmono (ε * g) (by positivity)) hlx
    have h2 : (1 - ε * g) * (216 * ℓ) ≤ (1 / 20) * (216 * (1 / 20)) := by
      have hlt : ℓ ≤ 1 / 20 := le_trans hlδ hsmall
      have h1' : 1 - ε * g ≤ 1 / 20 := le_trans h1 hsmall
      have hnn : 0 ≤ 1 - ε * g := by linarith
      calc (1 - ε * g) * (216 * ℓ) ≤ (1 / 20) * (216 * ℓ) :=
            mul_le_mul_of_nonneg_right h1' (by positivity)
        _ ≤ (1 / 20) * (216 * (1 / 20)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith
    nlinarith
  calc (1 - η * g) * (1 / g) ≤ (ε * g) * (1 / g) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ε := by field_simp

end StatisticalRL.Ch7Rest.FedSync

import Formalization.ModelFree.FiniteQ.Weights
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Constant bookkeeping for Theorem 4.13

Pure real arithmetic consequences of the printed schedule `eq:thm:finite-horizaon-eta`
(`chapters/generative_model_model_free.tex:2203–2209`) and sample-size condition
`eq:thm:finite-horizon-T` (:2220–2223) with `c₁ ≤ 1/64`, `0 < c₂ ≤ c₁` and `c₃ = 8000/c₂`.
Throughout `h = H ≥ 1`, `τ = T ≥ 2`, `l = log T`, `ℓ = log(SAT/δ)`. -/

open Finset

namespace StatisticalRL.FiniteQLearning

theorem log_two_gt : (0.6931 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

/-- The budget, cleared of denominators: `8000 h⁴ l³ ℓ ≤ c₂ ε² τ`. -/
theorem budget_clear {c₂ h l ℓ ε τ : ℝ} (hc₂ : 0 < c₂) (hε : 0 < ε)
    (hb : 8000 / c₂ * h ^ 4 * l ^ 3 * ℓ / ε ^ 2 ≤ τ) :
    8000 * h ^ 4 * l ^ 3 * ℓ ≤ c₂ * ε ^ 2 * τ := by
  have hε2 : 0 < ε ^ 2 := by positivity
  rw [div_le_iff₀ hε2] at hb
  have : 8000 / c₂ * h ^ 4 * l ^ 3 * ℓ * c₂ = 8000 * h ^ 4 * l ^ 3 * ℓ := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hb hc₂.le]

/-- `c₁ τ ≥ h l²`, so the lower schedule bound is at least `h l² / (2 c₁ τ)`. -/
theorem schedule_x_ge_one {c₁ c₂ h l ℓ ε τ : ℝ} (hc₂ : 0 < c₂) (hc₂₁ : c₂ ≤ c₁) (hh : 1 ≤ h)
    (hl : 0.6931 < l) (hℓ : l ≤ ℓ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ)
    (hb : 8000 * h ^ 4 * l ^ 3 * ℓ ≤ c₂ * ε ^ 2 * τ) : h * l ^ 2 ≤ c₁ * τ := by
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have h1 : c₂ * ε ^ 2 * τ ≤ c₁ * τ := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul hc₂₁ hε2 (sq_nonneg ε) (by linarith)) hτ.le
    nlinarith
  have hl0 : 0 < l := by linarith
  have hh4 : h ≤ h ^ 4 := by
    have : 1 ≤ h ^ 3 := one_le_pow₀ hh
    nlinarith
  have h2 : h * l ^ 2 ≤ 8000 * h ^ 4 * l ^ 3 * ℓ := by
    have hlℓ : 1 ≤ 8000 * l * ℓ := by nlinarith
    have : h * l ^ 2 ≤ h ^ 4 * l ^ 2 := mul_le_mul_of_nonneg_right hh4 (sq_nonneg l)
    have hp : 0 ≤ h ^ 4 * l ^ 2 := by positivity
    nlinarith
  linarith

/-- Upper rate on the late window: `η_k ≤ 2 h l² / (c₂ τ)` for `T/2 < k`. -/
theorem late_rate_le {c₂ h l : ℝ} {T k : ℕ} (hc₂ : 0 < c₂) (hhl : 0 < h * l ^ 2) (hT : 0 < T)
    (hk : T / 2 < k) {η : ℝ} (hη : η ≤ 1 / (1 + c₂ * k / (h * l ^ 2))) :
    η ≤ 2 * h * l ^ 2 / (c₂ * T) := by
  have hk2 : (T : ℝ) ≤ 2 * k := by
    have : T ≤ 2 * k := by omega
    exact_mod_cast this
  have hkpos : (0 : ℝ) < k := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hy : 0 < c₂ * k / (h * l ^ 2) := by positivity
  have h1 : 1 / (1 + c₂ * k / (h * l ^ 2)) ≤ 1 / (c₂ * k / (h * l ^ 2)) :=
    one_div_le_one_div_of_le hy (by linarith)
  rw [one_div_div] at h1
  refine hη.trans (h1.trans ?_)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hk2 (mul_nonneg hhl.le hc₂.le)]

/-- Lower rate: `η ≥ h l² / (2 c₁ τ)` once `h l² ≤ c₁ τ`. -/
theorem rate_ge {c₁ h l τ : ℝ} (hhl : 0 < h * l ^ 2) (hτ : 0 < τ) (hc₁ : 0 < c₁)
    (hx : h * l ^ 2 ≤ c₁ * τ) {η : ℝ} (hη : 1 / (1 + c₁ * τ / (h * l ^ 2)) ≤ η) :
    h * l ^ 2 / (2 * c₁ * τ) ≤ η := by
  refine le_trans ?_ hη
  have hx1 : 1 ≤ c₁ * τ / (h * l ^ 2) := by rw [le_div_iff₀ hhl]; linarith
  have h1 : 1 / (2 * (c₁ * τ / (h * l ^ 2))) ≤ 1 / (1 + c₁ * τ / (h * l ^ 2)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  refine le_of_eq_of_le ?_ h1
  field_simp

/-- `H 2^H e^{-8 H l²} ≤ H / T` for `l = log T ≥ log 2`. -/
theorem propagation_tail_le {H T : ℕ} (hH : 1 ≤ H) (hT : 2 ≤ T) :
    (H : ℝ) * 2 ^ H * Real.exp (-(8 * H * Real.log T ^ 2)) ≤ H / T := by
  have hq := log_two_gt
  have hTpos : (0 : ℝ) < T := by positivity
  have hl : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have h2 : (2 : ℝ) ^ H = Real.exp (H * Real.log 2) := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hT' : (1 : ℝ) / T = Real.exp (-Real.log T) := by
    rw [Real.exp_neg, Real.exp_log hTpos, one_div]
  rw [h2, mul_assoc, ← Real.exp_add, div_eq_mul_one_div, hT']
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  set q := Real.log 2
  set l := Real.log T
  have hkey : 0 ≤ 8 * l ^ 2 - l - q := by nlinarith
  have hneg : q - 8 * l ^ 2 ≤ 0 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ H) (by linarith : (0 : ℝ) ≤ 8 * l ^ 2 - q)]

/-- Consequences of the cleared budget: `H ≤ T` and `H / T ≤ ε / 6`. -/
theorem budget_consequences {c₁ c₂ h τ l ℓ ε : ℝ} (hc₂ : 0 < c₂) (hc₂₁ : c₂ ≤ c₁)
    (hc₁ : c₁ ≤ 1 / 64) (hh1 : 1 ≤ h) (hτ0 : 0 < τ) (hl : 0.6931 < l) (hℓ : l ≤ ℓ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 8000 * h ^ 4 * l ^ 3 * ℓ ≤ c₂ * ε ^ 2 * τ) :
    h ≤ τ ∧ h / τ ≤ ε / 6 := by
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hl4 : 0.23 ≤ l ^ 3 * ℓ := by
    have h3 : 0.6931 ^ 3 ≤ l ^ 3 := pow_le_pow_left₀ (by norm_num) hl.le 3
    have : 0.6931 ^ 3 * 0.6931 ≤ l ^ 3 * ℓ :=
      mul_le_mul h3 (by linarith) (by norm_num) (by positivity)
    norm_num at this
    linarith
  have hh4 : h ≤ h ^ 4 := by
    have : 1 ≤ h ^ 3 := one_le_pow₀ hh1
    nlinarith
  have hcε : c₂ * ε ^ 2 * τ ≤ ε * τ / 64 := by
    have h1 : c₂ * ε ^ 2 ≤ ε / 64 := by
      have := mul_le_mul (hc₂₁.trans hc₁) hε2 (by positivity) (by norm_num)
      linarith
    have := mul_le_mul_of_nonneg_right h1 hτ0.le
    linarith
  have hbig : 1840 * h ≤ ε * τ / 64 := by
    have h1 : h * 0.23 ≤ h ^ 4 * (l ^ 3 * ℓ) := mul_le_mul hh4 hl4 (by norm_num) (by positivity)
    have h2 : 8000 * h ^ 4 * l ^ 3 * ℓ = 8000 * (h ^ 4 * (l ^ 3 * ℓ)) := by ring
    linarith
  have hετ : ε * τ ≤ τ := by nlinarith
  refine ⟨by linarith, ?_⟩
  rw [div_le_iff₀ hτ0]
  linarith

/-- `log(8 S A H T / δ) ≤ 5 log(S A T / δ)` when `H ≤ T`, `T ≥ 2`, `S, A ≥ 1`, `δ ≤ 1`. -/
theorem log_confidence_le {S A h τ δ : ℝ} (hS : 1 ≤ S) (hA : 1 ≤ A) (hh : 0 < h) (hhτ : h ≤ τ)
    (hτ2 : 2 ≤ τ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (2 / (δ / (4 * S * A * h * τ))) ≤ 5 * Real.log (S * A * τ / δ) := by
  have hτ0 : 0 < τ := by linarith
  have hX : τ ≤ S * A * τ / δ := by
    rw [le_div_iff₀ hδ]
    have : 1 ≤ S * A := by nlinarith
    nlinarith
  set X := S * A * τ / δ with hX_def
  have heq : 2 / (δ / (4 * S * A * h * τ)) = 8 * h * X := by
    simp only [hX_def]; field_simp; ring
  have hX2 : 2 ≤ X := hτ2.trans hX
  have hX0 : 0 < X := by linarith
  have hX8 : 8 ≤ X ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hX2 3
    norm_num at this
    linarith
  have hhX : h ≤ X := hhτ.trans hX
  have hle : 8 * h * X ≤ X ^ 5 := by
    have h1 := mul_le_mul hX8 hhX hh.le (by positivity)
    have h2 : X ^ 3 * X * X = X ^ 5 := by ring
    have h3 : 8 * h * X ≤ X ^ 3 * X * X := mul_le_mul_of_nonneg_right h1 hX0.le
    linarith
  rw [heq]
  have := Real.log_le_log (by positivity) hle
  rwa [Real.log_pow] at this

/-- The radius bound `ρ H³ ≤ ε² / 64` with `ρ = 8 η̄ L`, `η̄ = 2 h l²/(c₂ τ)`, `L ≤ 5 ℓ`. -/
theorem rho_bound {c₂ h τ l ℓ ε L : ℝ} (hc₂ : 0 < c₂) (hh : 0 < h) (hτ0 : 0 < τ)
    (hl : 0.6931 < l) (hL0 : 0 ≤ L) (hL5 : L ≤ 5 * ℓ)
    (hb : 8000 * h ^ 4 * l ^ 3 * ℓ ≤ c₂ * ε ^ 2 * τ) :
    8 * (2 * h * l ^ 2 / (c₂ * τ)) * L * h ^ 3 ≤ ε ^ 2 / 64 := by
  have hl0 : 0 < l := by linarith
  have hexp : 8 * (2 * h * l ^ 2 / (c₂ * τ)) * L * h ^ 3 = 16 * h ^ 4 * l ^ 2 * L / (c₂ * τ) := by
    field_simp; ring
  rw [hexp, div_le_div_iff₀ (by positivity) (by norm_num)]
  have hp : 0 ≤ h ^ 4 * l ^ 2 := by positivity
  have h1 : 16 * h ^ 4 * l ^ 2 * L ≤ 80 * (h ^ 4 * l ^ 2 * ℓ) := by
    have := mul_le_mul_of_nonneg_left hL5 hp
    nlinarith
  have hℓ0 : 0 ≤ ℓ := by nlinarith
  have hq : 0 ≤ h ^ 4 * l ^ 2 * ℓ := by positivity
  have h2 : 80 * 64 * (h ^ 4 * l ^ 2 * ℓ) ≤ 8000 * h ^ 4 * l ^ 3 * ℓ := by
    have h3 : 8000 * h ^ 4 * l ^ 3 * ℓ = 8000 * l * (h ^ 4 * l ^ 2 * ℓ) := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right (by linarith) hq
  nlinarith

/-- Stability constants: with `λ = ε/(8h²)` and `D = 2 (h·2ρh + h ρ/(2λ) + λ h²)`, the stability
hypothesis holds and `D ≤ 7ε/16`, provided `ρ h³ ≤ ε²/64`. -/
theorem stability_constants {ρ h ε : ℝ} (hρ0 : 0 ≤ ρ) (hh1 : 1 ≤ h) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hρH : ρ * h ^ 3 ≤ ε ^ 2 / 64) :
    ∃ lam D : ℝ, 0 < lam ∧ 0 ≤ D ∧
      h * (2 * ρ * h + Real.sqrt (2 * ρ) * D + ρ / (2 * lam)) + lam * h ^ 2 ≤ D ∧
      D ≤ 7 * ε / 16 := by
  set lam := ε / (8 * h ^ 2) with hlam_def
  set D := 2 * (h * (2 * ρ * h) + h * (ρ / (2 * lam)) + lam * h ^ 2) with hD_def
  refine ⟨lam, D, ?_⟩
  have hh0 : 0 < h := by linarith
  have hlam : 0 < lam := by positivity
  have hρh2 : ρ * h ^ 2 ≤ ε ^ 2 / 64 := by
    have : ρ * h ^ 2 ≤ ρ * h ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ hρ0
      have : 1 ≤ h := hh1
      nlinarith
    linarith
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  set M := h * (2 * ρ * h) + h * (ρ / (2 * lam)) + lam * h ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hsq : h * Real.sqrt (2 * ρ) ≤ 1 / 2 := by
    have : h * Real.sqrt (2 * ρ) = Real.sqrt (2 * ρ * h ^ 2) := by
      rw [Real.sqrt_mul' _ (sq_nonneg h), Real.sqrt_sq hh0.le]; ring
    rw [this, Real.sqrt_le_left (by norm_num)]
    nlinarith
  refine ⟨hlam, hD0, ?_, ?_⟩
  · have h1 : h * (Real.sqrt (2 * ρ) * D) ≤ D / 2 := by
      have := mul_le_mul_of_nonneg_right hsq hD0
      nlinarith
    have hexp : h * (2 * ρ * h + Real.sqrt (2 * ρ) * D + ρ / (2 * lam)) + lam * h ^ 2 =
        M + h * (Real.sqrt (2 * ρ) * D) := by simp only [hM]; ring
    rw [hexp]
    have : D = 2 * M := rfl
    linarith
  · have h1 : h * (ρ / (2 * lam)) = 4 * (ρ * h ^ 3) / ε := by
      simp only [lam]; field_simp; ring
    have h2 : lam * h ^ 2 = ε / 8 := by simp only [lam]; field_simp
    have h3 : 4 * (ρ * h ^ 3) / ε ≤ ε / 16 := by
      rw [div_le_iff₀ hε]; nlinarith
    have h4 : h * (2 * ρ * h) ≤ ε / 32 := by nlinarith
    have : D = 2 * M := rfl
    rw [this, hM, h1, h2]
    linarith

end StatisticalRL.FiniteQLearning

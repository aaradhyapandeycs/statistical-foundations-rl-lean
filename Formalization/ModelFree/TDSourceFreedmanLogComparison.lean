import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option maxHeartbeats 1000000

/-!

Derive the source logarithmic comparison from the dyadic level and sample budget, with explicit sufficient constant `384≤c₃`.
-/

namespace StatisticalRL.TemporalDifference

/-- The source's dyadic level `2⌈log₂(1/(1−γ))⌉`. -/
noncomputable def tdSourceFreedmanLevel (γ : ℝ) : ℕ :=
  2 * Nat.ceil (Real.log (1 / (1 - γ)) / Real.log 2)

/-- Source sample-budget and cutoff conditions imply the logarithmic
comparison `log(4STK/δ) ≤ 3log(ST/δ)`. The explicit `c₃ ≥ 384` is a
sufficient universal threshold for this arithmetic derivation.

The proof derives the source cutoff `1/(1−γ) ≤ T` from the sample budget.
It also derives `T ≥ 48`, which is the lower bound used after the cutoff
bounds `K` by `4T`.
-/
theorem tdSourceBudget_logComparison
    (γ c₃ ε δ S : ℝ) (T : ℕ)
    (hT : 2 ≤ T) (hγhalf : 1 / 2 ≤ γ) (hγ1 : γ < 1)
    (hc₃ : 384 ≤ c₃) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hS : 1 ≤ S) (hε : 0 < ε)
    (hεmax : ε ≤ 1 / (1 - γ))
    (hBudget : c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log (S * T / δ) /
          ((1 - γ) ^ 3 * ε ^ 2) ≤ (T : ℝ)) :
    Real.log (4 * S * T * (tdSourceFreedmanLevel γ : ℝ) / δ) ≤
      3 * Real.log (S * T / δ) := by
  have hgap : 0 < 1 - γ := by linarith
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hlogT : 1 / 2 ≤ Real.log (T : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hmono : Real.log 2 ≤ Real.log (T : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hT)
    linarith
  have hSTtwo : 2 ≤ S * T := by
    have hTtwo : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith [mul_le_mul_of_nonneg_right hS (by positivity : 0 ≤ (T : ℝ))]
  have hq : 2 < S * T / δ := by
    rw [lt_div_iff₀ hδ]
    nlinarith [hδ1, hSTtwo]
  let q : ℝ := S * T / δ
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqgt : 2 < q := by simpa [q] using hq
  have hlogq : 1 / 2 ≤ Real.log q := by
    have h := Real.one_sub_inv_le_log_of_pos hqpos
    have hinv : q⁻¹ < 1 / 2 :=
      (inv_lt_iff_one_lt_mul₀' hqpos).2 (by nlinarith [hqgt])
    linarith
  have hc₃pos : 0 < c₃ := by linarith
  have hbudgetNum :
      c₃ * Real.log (T : ℝ) ^ 3 * Real.log q ≤
        (T : ℝ) * ((1 - γ) ^ 3 * ε ^ 2) := by
    have hden : 0 < (1 - γ) ^ 3 * ε ^ 2 :=
      mul_pos (pow_pos hgap 3) (sq_pos_of_pos hε)
    have hb := (div_le_iff₀ hden).mp (by simpa [q] using hBudget)
    simpa [q] using hb
  have hgapEps : (1 - γ) ^ 3 * ε ^ 2 ≤ 1 - γ := by
    have hx : (1 - γ) * ε ≤ 1 := by
      calc
        (1 - γ) * ε ≤ (1 - γ) * (1 / (1 - γ)) :=
          mul_le_mul_of_nonneg_left hεmax hgap.le
        _ = 1 := by field_simp
    have hxnonneg : 0 ≤ (1 - γ) * ε := mul_nonneg hgap.le hε.le
    have hx2 : ((1 - γ) * ε) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hxnonneg (sub_nonneg.mpr hx)]
    calc
      _ = (1 - γ) * ((1 - γ) * ε) ^ 2 := by ring
      _ ≤ (1 - γ) * 1 := mul_le_mul_of_nonneg_left hx2 hgap.le
      _ = 1 - γ := by ring
  have hbudgetGap :
      c₃ * Real.log (T : ℝ) ^ 3 * Real.log q ≤ (T : ℝ) * (1 - γ) := by
    calc
      _ ≤ (T : ℝ) * ((1 - γ) ^ 3 * ε ^ 2) := hbudgetNum
      _ ≤ (T : ℝ) * (1 - γ) :=
        mul_le_mul_of_nonneg_left hgapEps hTpos.le
  have hnumLower : 24 ≤
      c₃ * Real.log (T : ℝ) ^ 3 * Real.log q := by
    have hc₃half : 192 ≤ c₃ / 2 := by linarith
    have hlogTnonneg : 0 ≤ Real.log (T : ℝ) := by linarith
    have hlogTcube : 1 / 8 ≤ Real.log (T : ℝ) ^ 3 := by
      have hsquare : 1 / 4 ≤ Real.log (T : ℝ) ^ 2 := by nlinarith [hlogT]
      nlinarith [mul_le_mul_of_nonneg_left hsquare hlogTnonneg]
    have hlogqnonneg : 0 ≤ Real.log q := by linarith
    have hprod : c₃ / 16 ≤
        c₃ * Real.log (T : ℝ) ^ 3 * Real.log q := by
      have h1 := mul_le_mul_of_nonneg_left hlogTcube
        (mul_nonneg hc₃pos.le hlogqnonneg)
      have hcgq : c₃ / 2 ≤ c₃ * Real.log q := by
        have hh := mul_le_mul_of_nonneg_left hlogq hc₃pos.le
        nlinarith [hh]
      calc
        _ = c₃ / 16 := by ring
        _ ≤ (c₃ * Real.log q) / 8 := by nlinarith [hcgq]
        _ ≤ c₃ * Real.log (T : ℝ) ^ 3 * Real.log q := by nlinarith [h1]
    have : 24 ≤ c₃ / 16 := by nlinarith [hc₃]
    exact le_trans this hprod
  have hT48 : 48 ≤ (T : ℝ) := by
    have hnumReduced : 24 ≤ (T : ℝ) * (1 - γ) :=
      le_trans hnumLower hbudgetGap
    have hgapHalf : 1 - γ ≤ 1 / 2 := by linarith
    have hgapT := mul_le_mul_of_nonneg_left hgapHalf hTpos.le
    have hgapT' : (T : ℝ) * (1 - γ) ≤ (T : ℝ) / 2 := by
      nlinarith [hgapT]
    have hhalfT : 24 ≤ (T : ℝ) / 2 := by
      exact le_trans hnumReduced hgapT'
    nlinarith
  have hHleT : 1 / (1 - γ) ≤ (T : ℝ) := by
    rw [div_le_iff₀ hgap]
    have hnumReduced : 24 ≤ (T : ℝ) * (1 - γ) :=
      le_trans hnumLower hbudgetGap
    exact le_trans (by norm_num : (1 : ℝ) ≤ 24) hnumReduced
  have hHpos : 0 < 1 / (1 - γ) := by positivity
  have hHge2 : 2 ≤ 1 / (1 - γ) := by
    rw [le_div_iff₀ hgap]
    linarith
  have hlogHle : Real.log (1 / (1 - γ)) ≤ 1 / (1 - γ) := by
    have hh := Real.log_le_sub_one_of_pos hHpos
    linarith
  have hlog2 : 1 / 2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hlogHlower : Real.log 2 ≤ Real.log (1 / (1 - γ)) :=
    Real.log_le_log (by norm_num) hHge2
  have hquotLower :
      1 ≤ Real.log (1 / (1 - γ)) / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    nlinarith [hlogHlower]
  have hceilPos : 0 < Nat.ceil
      (Real.log (1 / (1 - γ)) / Real.log 2) := by
    have hceilLower := Nat.le_ceil
      (Real.log (1 / (1 - γ)) / Real.log 2)
    exact_mod_cast (le_trans hquotLower hceilLower)
  have hquot :
      Real.log (1 / (1 - γ)) / Real.log 2 ≤ 2 * (T : ℝ) := by
    rw [div_le_iff₀ (by linarith : 0 < Real.log 2)]
    have hmul := mul_le_mul_of_nonneg_right hlogHle (by positivity : 0 ≤ Real.log 2)
    have hmul2 := mul_le_mul_of_nonneg_left hHleT (by positivity : 0 ≤ Real.log 2)
    nlinarith [hlog2, hmul, hmul2]
  have hceil : Nat.ceil
      (Real.log (1 / (1 - γ)) / Real.log 2) ≤ 2 * T := by
    apply Nat.ceil_le.mpr
    exact_mod_cast hquot
  have hKbound : (tdSourceFreedmanLevel γ : ℝ) ≤ 4 * T := by
    unfold tdSourceFreedmanLevel
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hmul := Nat.mul_le_mul_left 2 hceil
    have hnat : 2 * Nat.ceil
        (Real.log (1 / (1 - γ)) / Real.log 2) ≤ 4 * T := by omega
    exact_mod_cast hnat
  have hqLower : (T : ℝ) ≤ q := by
    dsimp [q]
    rw [le_div_iff₀ hδ]
    nlinarith [hS, hδ1, hTpos]
  have hq2 : 4 * (tdSourceFreedmanLevel γ : ℝ) ≤ q ^ 2 := by
    have hqSq : (T : ℝ) ^ 2 ≤ q ^ 2 := by nlinarith [hqLower, hTpos]
    have hTsqLinear : 16 * (T : ℝ) ≤ (T : ℝ) ^ 2 := by
      nlinarith [hT48]
    calc
      _ ≤ 16 * (T : ℝ) := by nlinarith [hKbound]
      _ ≤ (T : ℝ) ^ 2 := hTsqLinear
      _ ≤ q ^ 2 := hqSq
  have hargpos : 0 < 4 * S * T * (tdSourceFreedmanLevel γ : ℝ) / δ := by
    have hKpos : 0 < (tdSourceFreedmanLevel γ : ℝ) := by
      unfold tdSourceFreedmanLevel
      exact_mod_cast (Nat.mul_pos (by decide) hceilPos)
    positivity
  have hargle :
      4 * S * T * (tdSourceFreedmanLevel γ : ℝ) / δ ≤ q ^ 3 := by
    have hmulq := mul_le_mul_of_nonneg_right hq2 hqpos.le
    calc
      _ = 4 * (tdSourceFreedmanLevel γ : ℝ) * q := by
        dsimp [q]
        field_simp [ne_of_gt hδ]
      _ ≤ q ^ 3 := by nlinarith [hmulq]
  have hlogmono := Real.log_le_log hargpos hargle
  rw [Real.log_pow] at hlogmono
  simpa [q] using hlogmono

end StatisticalRL.TemporalDifference

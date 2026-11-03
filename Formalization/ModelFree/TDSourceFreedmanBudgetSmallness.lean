import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!

Normalize the printed TD sample budget into the source bar-eta and second-Freedman smallness inputs. The source logarithm comparison remains an explicit dependency.
-/

namespace StatisticalRL.TemporalDifference

/-- The source late-rate envelope `2 log^3(T)/((1−γ)T)`. -/
noncomputable def tdSourceBarEta (γ : ℝ) (T : ℕ) : ℝ :=
  2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T)

/-- The finite sample-budget condition and source logarithm comparison imply
the exact per-coordinate smallness used by the terminal union. The logarithm
uses `δ/(2ST)`, while the theorem's source budget uses `log(ST/δ)`.

The sufficient universal threshold `384≤c₃` is explicit. The source says
only “sufficiently large”; this theorem records a simple sufficient value for
this specific second-Freedman substitution. -/
theorem tdSourceBudget_to_barEta_smallness
    (γ c₃ ε δ S : ℝ) (T K : ℕ)
    (hT : 2 ≤ T) (hγhalf : 1 / 2 ≤ γ) (hγ1 : γ < 1)
    (hc₃ : 384 ≤ c₃) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hS : 1 ≤ S) (hε : 0 < ε)
    (hεmax : ε ≤ 1 / (1 - γ)) (hK : 0 < K)
    (hBudget : c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log (S * T / δ) /
          ((1 - γ) ^ 3 * ε ^ 2) ≤ (T : ℝ))
    (hLogBound : Real.log (4 * S * T * K / δ) ≤
        3 * Real.log (S * T / δ)) :
    0 ≤ tdSourceBarEta γ T ∧ tdSourceBarEta γ T ≤ 1 / 2 ∧
      tdSourceBarEta γ T * Real.log
        (2 * K / (δ / (2 * S * T))) ≤ 1 / 64 := by
  have hgap : 0 < 1 - γ := by linarith
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hlogT : 0 < Real.log (T : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < T)
  have hST : 2 ≤ S * T := by
    have hTtwo : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith [mul_le_mul_of_nonneg_right hS (by positivity : 0 ≤ (T : ℝ))]
  have hq : 2 < S * T / δ := by
    rw [lt_div_iff₀ hδ]
    nlinarith [hδ1, hST]
  have hqpos : 0 < S * T / δ := lt_trans (by norm_num) hq
  have hlogqHalf : 1 / 2 < Real.log (S * T / δ) := by
    have hinv := Real.one_sub_inv_le_log_of_pos hqpos
    have hinvSmall : 1 / (S * T / δ) < 1 / 2 := by
      rw [div_lt_iff₀ hqpos]
      nlinarith [hq]
    have hinvSmall' : (S * T / δ)⁻¹ < 1 / 2 := by
      simpa only [one_div] using hinvSmall
    calc
      1 / 2 < 1 - (S * T / δ)⁻¹ := by linarith
      _ ≤ Real.log (S * T / δ) := hinv
  have hc₃pos : 0 < c₃ := by linarith
  have hlogqpos : 0 < Real.log (S * T / δ) := by linarith
  have hc₃log : 4 ≤ c₃ * Real.log (S * T / δ) := by
    have hprod : c₃ / 2 ≤ c₃ * Real.log (S * T / δ) := by
      have hh := mul_le_mul_of_nonneg_left hlogqHalf.le hc₃pos.le
      nlinarith [hh]
    have hhalf : 4 ≤ c₃ / 2 := by nlinarith [hc₃]
    exact le_trans hhalf hprod
  have hbudgetNumerator :
      c₃ * Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ) ≤
        (T : ℝ) * ((1 - γ) ^ 3 * ε ^ 2) := by
    have hden : 0 < (1 - γ) ^ 3 * ε ^ 2 :=
      mul_pos (pow_pos hgap 3) (sq_pos_of_pos hε)
    exact (div_le_iff₀ hden).mp hBudget
  have hgapEps : (1 - γ) ^ 3 * ε ^ 2 ≤ 1 - γ := by
    have hgeps : (1 - γ) * ε ≤ 1 := by
      calc
        (1 - γ) * ε ≤ (1 - γ) * (1 / (1 - γ)) :=
          mul_le_mul_of_nonneg_left hεmax hgap.le
        _ = 1 := by field_simp
    have hxnonneg : 0 ≤ (1 - γ) * ε := mul_nonneg hgap.le hε.le
    have hxSq : ((1 - γ) * ε) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hxnonneg (sub_nonneg.mpr hgeps)]
    calc
      _ = (1 - γ) * ((1 - γ) * ε) ^ 2 := by ring
      _ ≤ (1 - γ) * 1 := mul_le_mul_of_nonneg_left hxSq hgap.le
      _ = 1 - γ := by ring
  have hbudgetReduced :
      c₃ * Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ) ≤
        (T : ℝ) * (1 - γ) := by
    calc
      _ ≤ (T : ℝ) * ((1 - γ) ^ 3 * ε ^ 2) := hbudgetNumerator
      _ ≤ (T : ℝ) * (1 - γ) :=
        mul_le_mul_of_nonneg_left hgapEps hTreal.le
  have hbarBound : tdSourceBarEta γ T ≤
      2 / (c₃ * Real.log (S * T / δ)) := by
    unfold tdSourceBarEta
    rw [div_le_div_iff₀ (mul_pos hgap hTreal)
      (mul_pos hc₃pos hlogqpos)]
    nlinarith [hbudgetReduced]
  have hbarHalf : tdSourceBarEta γ T ≤ 1 / 2 := by
    have hratio : 2 / (c₃ * Real.log (S * T / δ)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (mul_pos hc₃pos hlogqpos)]
      nlinarith [hc₃log]
    exact le_trans hbarBound hratio
  have harg : 2 * K / (δ / (2 * S * T)) = 4 * S * T * K / δ := by
    have hSTpos : 0 < S * T := by linarith
    field_simp [ne_of_gt hδ, ne_of_gt hSTpos]
    ring
  have hbarNonneg : 0 ≤ tdSourceBarEta γ T := by
    unfold tdSourceBarEta
    positivity
  have hsmall :
      tdSourceBarEta γ T * Real.log (2 * K / (δ / (2 * S * T))) ≤ 1 / 64 := by
    rw [harg]
    calc
      _ ≤ tdSourceBarEta γ T * (3 * Real.log (S * T / δ)) :=
        mul_le_mul_of_nonneg_left hLogBound hbarNonneg
      _ ≤ (2 / (c₃ * Real.log (S * T / δ))) *
          (3 * Real.log (S * T / δ)) :=
        mul_le_mul_of_nonneg_right hbarBound (by positivity)
      _ = 6 / c₃ := by field_simp [ne_of_gt hc₃pos]; ring
      _ ≤ 1 / 64 := by
        rw [div_le_iff₀ hc₃pos]
        nlinarith [hc₃]
  exact ⟨hbarNonneg, hbarHalf, hsmall⟩

end StatisticalRL.TemporalDifference

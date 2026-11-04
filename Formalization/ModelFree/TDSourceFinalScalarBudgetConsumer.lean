import Mathlib
import Formalization.ModelFree.TDSourceFinalScalarBudgetBridge
import Formalization.ModelFree.TDSourceFinalScalarArithmetic

/-! Source-facing scalar-consumer helper for the TD accuracy composition. It
combines the stated terminal-budget consequences with the arithmetic bounds
while keeping the source theorem's conditions explicit. -/

set_option maxHeartbeats 500000

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

/-- Cancel the positive `ε^3` factor in the two named terminal-budget bounds. -/
private theorem terminal_budget_absorption
    (H ε T c₃ : ℝ) (hε : 0 < ε)
    (hweighted : c₃ ^ 2 * H ^ 6 ≤ 256 * ε ^ 4 * T ^ 2)
    (hneeded : 1024 * ε ^ 3 * H ≤ c₃ ^ 2 * H ^ 6) :
    4 * H ≤ ε * T ^ 2 := by
  have hscaled : (4 * H) * (256 * ε ^ 3) ≤ (ε * T ^ 2) * (256 * ε ^ 3) := by
    calc
      (4 * H) * (256 * ε ^ 3) = 1024 * ε ^ 3 * H := by ring
      _ ≤ c₃ ^ 2 * H ^ 6 := hneeded
      _ ≤ 256 * ε ^ 4 * T ^ 2 := hweighted
      _ = (ε * T ^ 2) * (256 * ε ^ 3) := by ring
  have hscaled' : (256 * ε ^ 3) * (4 * H) ≤
      (256 * ε ^ 3) * (ε * T ^ 2) := by
    simpa only [mul_comm] using hscaled
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 256 * ε ^ 3)).mp hscaled'

/-- Scalar source-radius absorption once the original variance is at its
33-scale. The sample budget controls the square-root and linear Freedman
terms; the initial term `H/T²` is absorbed using the same budget and
`ε≤H`. The explicit sufficient choice is `c₃≥3168`. -/
theorem tdSource_final_scalar_absorption
    (γ H ε δ S c₃ : ℝ) (T : ℕ)
    (hγhalf : 1 / 2 ≤ γ) (hγ1 : γ < 1)
    (hH : H = 1 / (1 - γ)) (hHge2 : 2 ≤ H)
    (hT : 2 ≤ T) (hS : 1 ≤ S)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hεH : ε ≤ H)
    (hc₃ : 3168 ≤ c₃)
    (hBudget : c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log (S * T / δ) / ((1 - γ) ^ 3 * ε ^ 2) ≤ (T : ℝ)) :
    Real.sqrt (8 * (33 * Real.log (T : ℝ) ^ 3 /
        ((1 - γ) ^ 3 * T)) * (3 * Real.log (S * T / δ))) ≤ ε / 2 ∧
      (4 / 3) * (4 * γ * Real.log (T : ℝ) ^ 3 /
        ((1 - γ) ^ 2 * T)) * (3 * Real.log (S * T / δ)) ≤ ε / 4 ∧
      H / (T : ℝ) ^ 2 ≤ ε / 4 := by
  have hgap : 0 < 1 - γ := sub_pos.mpr hγ1
  have hgapLe : 1 - γ ≤ 1 := by linarith
  have hgamma0 : 0 ≤ γ := by linarith
  have hgammaLe : γ ≤ 1 := by linarith
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hlogT : 1 / 2 ≤ Real.log (T : ℝ) := by
    have hlog2 : Real.log 2 ≤ Real.log (T : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hT)
    have hlog2half : 1 / 2 ≤ Real.log 2 := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      linarith
    exact hlog2half.trans hlog2
  have hlogT0 : 0 ≤ Real.log (T : ℝ) := by linarith
  have hST : 2 ≤ S * T := by
    have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith [mul_le_mul_of_nonneg_right hS (by positivity : 0 ≤ (T : ℝ))]
  have hq : 2 < S * T / δ := by
    rw [lt_div_iff₀ hδ]
    nlinarith [hST, hδ1]
  have hqpos : 0 < S * T / δ := by positivity
  have hlogq : 1 / 2 ≤ Real.log (S * T / δ) := by
    have hlogineq := Real.one_sub_inv_le_log_of_pos hqpos
    have hinv : (S * T / δ)⁻¹ < 1 / 2 := by
      rw [inv_lt_iff_one_lt_mul₀' hqpos]
      nlinarith [hq]
    linarith
  have hlogq0 : 0 ≤ Real.log (S * T / δ) := by linarith
  have hlogs : 1 / 16 ≤ Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ) := by
    have hprod := mul_le_mul hlogT hlogq
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      hlogT0
    have hcube : 1 / 8 ≤ Real.log (T : ℝ) ^ 3 := by
      nlinarith [sq_nonneg (Real.log (T : ℝ))]
    have hmul := mul_le_mul_of_nonneg_right hprod (pow_nonneg hlogT0 2)
    nlinarith [hmul, hcube]
  have hden : 0 < (1 - γ) ^ 3 * ε ^ 2 :=
    mul_pos (pow_pos hgap 3) (sq_pos_of_pos hε)
  have hbudgetNum : c₃ * Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ) ≤
      (T : ℝ) * ((1 - γ) ^ 3 * ε ^ 2) :=
    (div_le_iff₀ hden).mp hBudget
  have hc₃pos : 0 < c₃ := by linarith
  have hTlowerNum : c₃ / 16 ≤ (T : ℝ) * (1 - γ) ^ 3 * ε ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlogs hc₃pos.le
    calc
      c₃ / 16 ≤ c₃ * (Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ)) := by
        nlinarith [h]
      _ = c₃ * Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ) := by ring
      _ ≤ (T : ℝ) * ((1 - γ) ^ 3 * ε ^ 2) := hbudgetNum
      _ = (T : ℝ) * (1 - γ) ^ 3 * ε ^ 2 := by ring
  have hTlower : c₃ / (16 * (1 - γ) ^ 3 * ε ^ 2) ≤ (T : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * (1 - γ) ^ 3 * ε ^ 2)).2
    nlinarith [hTlowerNum]
  let X : ℝ := Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ) /
    ((1 - γ) ^ 3 * (T : ℝ))
  have hX : X ≤ ε ^ 2 / c₃ := by
    simpa [X] using
      td_source_scalar_X_le_of_budget γ ε δ S c₃ T
        hγ1 hε hc₃pos hTpos hBudget
  have hrootArg :
      8 * (33 * Real.log (T : ℝ) ^ 3 /
        ((1 - γ) ^ 3 * T)) * (3 * Real.log (S * T / δ)) ≤
      ((1 / 2 : ℝ) * ε) ^ 2 := by
    have hcoef : 792 / c₃ ≤ 1 / 4 := by
      have hscaled : (792 : ℝ) * 4 ≤ c₃ := by nlinarith [hc₃]
      rw [div_le_iff₀ hc₃pos]
      norm_num
      linarith [hscaled]
    have heq : 8 * (33 * Real.log (T : ℝ) ^ 3 /
        ((1 - γ) ^ 3 * T)) * (3 * Real.log (S * T / δ)) = 792 * X := by
      dsimp [X]
      ring
    rw [heq]
    calc
      792 * X ≤ 792 * (ε ^ 2 / c₃) :=
        mul_le_mul_of_nonneg_left hX (by norm_num)
      _ = (792 / c₃) * ε ^ 2 := by ring
      _ ≤ (1 / 4) * ε ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg ε)
      _ = ((1 / 2 : ℝ) * ε) ^ 2 := by ring
  have hroot : Real.sqrt
      (8 * (33 * Real.log (T : ℝ) ^ 3 /
        ((1 - γ) ^ 3 * T)) * (3 * Real.log (S * T / δ))) ≤ ε / 2 := by
    have h := Real.sqrt_le_sqrt hrootArg
    rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) * ε)] at h
    have hhalf : (1 / 2 : ℝ) * ε = ε / 2 := by ring
    rw [hhalf] at h
    exact h
  have hlinear :
      (4 / 3) * (4 * γ * Real.log (T : ℝ) ^ 3 /
        ((1 - γ) ^ 2 * T)) * (3 * Real.log (S * T / δ)) ≤ ε / 4 := by
    have hεgap : (1 - γ) * ε ≤ 1 := by
      rw [hH] at hεH
      calc
        (1 - γ) * ε = ε * (1 - γ) := by ring
        _ ≤ 1 := (le_div_iff₀ hgap).mp hεH
    have heq :
        (4 / 3) * (4 * γ * Real.log (T : ℝ) ^ 3 /
          ((1 - γ) ^ 2 * T)) * (3 * Real.log (S * T / δ)) =
        16 * γ * (1 - γ) * X := by
      dsimp [X]
      field_simp [ne_of_gt hTpos]
      ring
    rw [heq]
    exact td_source_scalar_linear_absorption γ (1 - γ) ε X c₃
      hgamma0 hgammaLe hgap.le hεgap hε hc₃ hX
  have hHpos : 0 < H := by rw [hH]; positivity
  have hTlowH : c₃ * H ^ 3 / (16 * ε ^ 2) ≤ (T : ℝ) := by
    rw [hH]
    field_simp [ne_of_gt hgap, ne_of_gt hε] at hTlower ⊢
    nlinarith [hTlower]
  have hTlowSq : c₃ ^ 2 * H ^ 6 / (256 * ε ^ 4) ≤ (T : ℝ) ^ 2 := by
    have hxnonneg : 0 ≤ c₃ * H ^ 3 / (16 * ε ^ 2) := by positivity
    have hTnonneg : 0 ≤ (T : ℝ) := by positivity
    have hsq := (sq_le_sq₀ hxnonneg hTnonneg).2 hTlowH
    calc
      c₃ ^ 2 * H ^ 6 / (256 * ε ^ 4) =
          (c₃ * H ^ 3 / (16 * ε ^ 2)) ^ 2 := by
            field_simp [ne_of_gt hε]
            ring
      _ ≤ (T : ℝ) ^ 2 := hsq
  have hc₃sq : 256 ≤ c₃ ^ 2 := by nlinarith
  have hHsq : 4 ≤ H ^ 2 := by nlinarith [hHge2]
  have hc₃Hsq : 1024 ≤ c₃ ^ 2 * H ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hc₃sq (sq_nonneg H)
    nlinarith [hmul, hHsq]
  have hepscube : ε ^ 3 ≤ H ^ 3 := by
    exact pow_le_pow_left₀ (by positivity) hεH 3
  have hinitial : H / (T : ℝ) ^ 2 ≤ ε / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < (T : ℝ) ^ 2)).2
    have hneeded : 1024 * ε ^ 3 ≤ c₃ ^ 2 * H ^ 5 := by
      have heps3nonneg : 0 ≤ ε ^ 3 := by positivity
      have hcoefnonneg : 0 ≤ c₃ ^ 2 * H ^ 2 := by positivity
      calc
        1024 * ε ^ 3 ≤ (c₃ ^ 2 * H ^ 2) * ε ^ 3 :=
          mul_le_mul_of_nonneg_right hc₃Hsq heps3nonneg
        _ ≤ (c₃ ^ 2 * H ^ 2) * H ^ 3 :=
          mul_le_mul_of_nonneg_left hepscube hcoefnonneg
        _ = c₃ ^ 2 * H ^ 5 := by ring
    have hneededH : 1024 * ε ^ 3 * H ≤ c₃ ^ 2 * H ^ 6 := by
      have hh := mul_le_mul_of_nonneg_right hneeded hHpos.le
      calc
        1024 * ε ^ 3 * H ≤ (c₃ ^ 2 * H ^ 5) * H := hh
        _ = c₃ ^ 2 * H ^ 6 := by ring
    have hTweighted := mul_le_mul_of_nonneg_left hTlowSq (by positivity : 0 ≤ ε / 4)
    field_simp [ne_of_gt hε] at hTweighted hneeded ⊢
    have hTweighted' : c₃ ^ 2 * H ^ 6 ≤ 256 * ε ^ 4 * (T : ℝ) ^ 2 := by
      simpa only [mul_comm] using hTweighted
    exact terminal_budget_absorption H ε (T : ℝ) c₃ hε hTweighted' hneededH
  exact ⟨hroot, hlinear, hinitial⟩


end StatisticalRL.TemporalDifference

import Mathlib

/-! Pure-real inequalities used in the TD final-scalar absorption. The helper
lemmas isolate the algebra without changing any source-facing theorem or
source condition. -/

namespace StatisticalRL.TemporalDifference

/-- The source linear contribution's epsilon product, isolated from the
large MDP/event context. -/
theorem td_source_scalar_gamma_gap_epsilon_sq_le
    (γ α ε : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hα0 : 0 ≤ α) (hαε : α * ε ≤ 1)
    (hε0 : 0 ≤ ε) :
    γ * α * ε ^ 2 ≤ ε := by
  have hγε : γ * ε ≤ ε := by
    calc
      γ * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right hγ1 hε0
      _ = ε := by ring
  have hαε0 : 0 ≤ α * ε := mul_nonneg hα0 hε0
  calc
    γ * α * ε ^ 2 = (γ * ε) * (α * ε) := by ring
    _ ≤ ε * (α * ε) := mul_le_mul_of_nonneg_right hγε hαε0
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hαε hε0
    _ = ε := by ring

/-- The source universal-constant choice absorbs the scalar linear
coefficient. -/
theorem td_source_scalar_linear_coefficient_le_quarter
    (c₃ : ℝ) (hc₃ : 3168 ≤ c₃) :
    16 / c₃ ≤ 1 / 4 := by
  have hc₃pos : 0 < c₃ := by linarith
  rw [div_le_iff₀ hc₃pos]
  nlinarith

/-- Isolate the complete linear-term absorption from the larger final scalar
theorem. The input `hX` is exactly the budget consequence already derived in
the source proof; no source-side assumption is added. -/
theorem td_source_scalar_linear_absorption
    (γ α ε X c₃ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hα0 : 0 ≤ α) (hαε : α * ε ≤ 1)
    (hε : 0 < ε) (hc₃ : 3168 ≤ c₃)
    (hX : X ≤ ε ^ 2 / c₃) :
    16 * γ * α * X ≤ ε / 4 := by
  have hc₃pos : 0 < c₃ := by linarith
  have hcoef : 16 / c₃ ≤ 1 / 4 :=
    td_source_scalar_linear_coefficient_le_quarter c₃ hc₃
  have hterm := td_source_scalar_gamma_gap_epsilon_sq_le γ α ε
    hγ0 hγ1 hα0 hαε hε.le
  have hfactor : 0 ≤ 16 * γ * α := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hX hfactor
  calc
    16 * γ * α * X = (16 * γ * α) * X := by ring
    _ ≤ (16 * γ * α) * (ε ^ 2 / c₃) := hscaled
    _ = (16 / c₃) * (γ * α * ε ^ 2) := by
      field_simp [ne_of_gt hc₃pos]
    _ ≤ (16 / c₃) * ε :=
      mul_le_mul_of_nonneg_left hterm (by positivity)
    _ ≤ ε / 4 := by
      calc
        (16 / c₃) * ε ≤ (1 / 4) * ε :=
          mul_le_mul_of_nonneg_right hcoef hε.le
        _ = ε / 4 := by ring

/-- The root-term coefficient bound used alongside the linear absorption. -/
theorem td_source_scalar_root_coefficient_le_quarter
    (c₃ : ℝ) (hc₃ : 3168 ≤ c₃) :
    792 / c₃ ≤ 1 / 4 := by
  have hc₃pos : 0 < c₃ := by linarith
  rw [div_le_iff₀ hc₃pos]
  nlinarith

end StatisticalRL.TemporalDifference

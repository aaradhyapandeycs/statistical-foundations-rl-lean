import Mathlib

/-! Derive the normalized logarithmic-factor bound used by the final scalar
absorption from the printed finite-horizon sample budget. -/

namespace StatisticalRL.TemporalDifference

/-- The printed finite-T budget controls the normalized logarithmic factor
used by the final scalar absorption. This is a pure algebraic consequence of
the actual source budget; `X` is defined by its source expression. -/
theorem td_source_scalar_X_le_of_budget
    (γ ε δ S c₃ : ℝ) (T : ℕ)
    (hγ : γ < 1) (hε : 0 < ε) (hc₃ : 0 < c₃) (hT : 0 < (T : ℝ))
    (hBudget : c₃ * Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ) /
        ((1 - γ) ^ 3 * ε ^ 2) ≤ (T : ℝ)) :
    let X := Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ) /
      ((1 - γ) ^ 3 * (T : ℝ))
    X ≤ ε ^ 2 / c₃ := by
  have hgap : 0 < 1 - γ := sub_pos.mpr hγ
  have hbudgetDen : 0 < (1 - γ) ^ 3 * ε ^ 2 :=
    mul_pos (pow_pos hgap 3) (sq_pos_of_pos hε)
  have hbudgetNumerator :
      c₃ * (Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ)) ≤
        (T : ℝ) * ((1 - γ) ^ 3 * ε ^ 2) := by
    have h := (div_le_iff₀ hbudgetDen).mp hBudget
    simpa only [mul_assoc] using h
  dsimp
  apply (div_le_div_iff₀
    (mul_pos (pow_pos hgap 3) hT) hc₃).2
  calc
    Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ) * c₃ =
        c₃ * (Real.log (T : ℝ) ^ 3 * Real.log (S * T / δ)) := by ring
    _ ≤ (T : ℝ) * ((1 - γ) ^ 3 * ε ^ 2) := hbudgetNumerator
    _ = ε ^ 2 * ((1 - γ) ^ 3 * (T : ℝ)) := by ring

end StatisticalRL.TemporalDifference

import Formalization.ModelFree.TDTerminalWeightEnvelope

/-! Derive the first-Freedman increment and crude predictable-variance scales
from the actual finite rate schedule. The source scales are conclusions rather
than assumptions; the dyadic and logarithmic comparisons are separate results. -/

namespace StatisticalRL.TemporalDifference

/-- For T≥2 and γ≥1/2, the early T⁻² branch of the existing terminal weight
envelope is dominated by its late-rate branch. -/
theorem tdSource_terminalWeightEnvelope_le_late
    (γ : ℝ) (T : ℕ) (hT : 2 ≤ T) (hγhalf : 1 / 2 ≤ γ) (hγ1 : γ < 1) :
    tdTerminalWeightEnvelope γ T ≤
      2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T) := by
  have hgap : 0 < 1 - γ := sub_pos.mpr hγ1
  have hgapHalf : 1 - γ ≤ 1 / 2 := by linarith
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlogT : Real.log 2 ≤ Real.log (T : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hlogHalf : 1 / 2 ≤ Real.log (T : ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh.trans hlogT
  have hlogPos : 0 < Real.log (T : ℝ) := by positivity
  have hTpos : 0 < (T : ℝ) := by positivity
  have hden : 0 < (1 - γ) * T := mul_pos hgap hTpos
  have hearly : 1 / (T : ℝ) ^ 2 ≤
      2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T) := by
    apply (div_le_div_iff₀ (pow_pos hTpos 2) hden).2
    have hcube : (1 / 2 : ℝ) ^ 3 ≤ Real.log (T : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hlogHalf 3
    have hmul := mul_le_mul_of_nonneg_left hcube
      (by positivity : 0 ≤ 2 * (T : ℝ))
    have hgapBound : (1 - γ) ≤ 2 * (T : ℝ) * Real.log (T : ℝ) ^ 3 := by
      nlinarith [hgapHalf, hTr, hmul]
    have hgapBound' := mul_le_mul_of_nonneg_right hgapBound hTpos.le
    nlinarith [hgapBound']
  unfold tdTerminalWeightEnvelope
  exact max_le hearly le_rfl

/-- For a source terminal, all actual rate weights have the late source
envelope. The resulting B and σ² caps match the source's first-Freedman
scales before the separate dyadic division by 2ᴷ. -/
theorem tdSource_freedman_schedule_weight_caps
    (γ c₁ c₂ : ℝ) (T t : ℕ) (η : ℕ → ℝ)
    (hT : 2 ≤ T) (hγhalf : 1 / 2 ≤ γ) (hγ1 : γ < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hcprod : c₁ * c₂ ≤ 1 / 8)
    (hlarge : Real.log (T : ℝ) ^ 2 ≤ c₁ * (1 - γ) * T)
    (hs : TDStepSizeSchedule γ c₁ c₂ T η)
    (ht : t ≤ T)
    (htime : (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ t) :
    (∀ k, 1 ≤ k → k ≤ t →
      tdRateWeight γ η t k ≤
        2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T)) ∧
    2 * γ * (1 / (1 - γ)) * tdTerminalWeightEnvelope γ T ≤
      4 * γ * Real.log (T : ℝ) ^ 3 / ((1 - γ) ^ 2 * T) ∧
    γ ^ 2 * (1 / (1 - γ)) ^ 3 * tdTerminalWeightEnvelope γ T ≤
      3 * Real.log (T : ℝ) ^ 3 / ((1 - γ) ^ 4 * T) := by
  have hγ0 : 0 ≤ γ := by linarith
  have hgap : 0 < 1 - γ := sub_pos.mpr hγ1
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hA : tdTerminalWeightEnvelope γ T ≤
      2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T) :=
    tdSource_terminalWeightEnvelope_le_late γ T hT hγhalf hγ1
  have hA0 : 0 ≤ tdTerminalWeightEnvelope γ T :=
    tdTerminalWeightEnvelope_nonneg γ T
  have hweight : ∀ k, 1 ≤ k → k ≤ t →
      tdRateWeight γ η t k ≤ tdTerminalWeightEnvelope γ T := by
    intro k hk1 hkt
    exact tdRateWeight_le_terminalEnvelope γ c₁ c₂ T η hT (by linarith)
      hγ1 hc₁ hc₂ hcprod hlarge hs t ht htime k hk1 hkt
  have hweightsmall : ∀ k, 1 ≤ k → k ≤ t →
      tdRateWeight γ η t k ≤
        2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T) := by
    intro k hk1 hkt
    exact (hweight k hk1 hkt).trans hA
  have hB : 2 * γ * (1 / (1 - γ)) * tdTerminalWeightEnvelope γ T ≤
      4 * γ * Real.log (T : ℝ) ^ 3 / ((1 - γ) ^ 2 * T) := by
    have hmul := mul_le_mul_of_nonneg_left hA
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hγ0)
        (by positivity : 0 ≤ 1 / (1 - γ)))
    calc
      _ ≤ 2 * γ * (1 / (1 - γ)) *
          (2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T)) := hmul
      _ = 4 * γ * Real.log (T : ℝ) ^ 3 /
          ((1 - γ) ^ 2 * T) := by field_simp; ring
  have hσ : γ ^ 2 * (1 / (1 - γ)) ^ 3 * tdTerminalWeightEnvelope γ T ≤
      3 * Real.log (T : ℝ) ^ 3 / ((1 - γ) ^ 4 * T) := by
    have hγsq : γ ^ 2 ≤ 1 := by nlinarith
    have hcoef : 0 ≤ (1 / (1 - γ)) ^ 3 := by positivity
    have hlogNonneg : 0 ≤ Real.log (T : ℝ) := by
      exact (Real.log_pos (by exact_mod_cast (by omega : 1 < T))).le
    calc
      _ ≤ γ ^ 2 * (1 / (1 - γ)) ^ 3 *
          (2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T)) :=
        mul_le_mul_of_nonneg_left hA
          (mul_nonneg (sq_nonneg γ) hcoef)
      _ = 2 * γ ^ 2 * Real.log (T : ℝ) ^ 3 /
          ((1 - γ) ^ 4 * T) := by field_simp
      _ ≤ 3 * Real.log (T : ℝ) ^ 3 / ((1 - γ) ^ 4 * T) := by
        have hγfactor : 2 * γ ^ 2 ≤ 3 := by nlinarith
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hγfactor
            (pow_nonneg hlogNonneg 3)) (by positivity)
  exact ⟨hweightsmall, hB, hσ⟩

end StatisticalRL.TemporalDifference

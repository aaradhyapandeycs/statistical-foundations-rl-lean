import Formalization.ModelFree.TDStepSizeBudget

/-! Actual finite schedule to a safe common weight envelope.
The explicit max avoids silently absorbing the source early-time term.
Large-T contraction and late-terminal feasibility are distinct obligations. -/
namespace StatisticalRL.TemporalDifference

noncomputable def tdTerminalWeightEnvelope (γ : ℝ) (T : ℕ) : ℝ :=
  max (1 / (T : ℝ) ^ 2) (2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T))

theorem tdTerminalWeightEnvelope_nonneg (γ : ℝ) (T : ℕ) :
    0 ≤ tdTerminalWeightEnvelope γ T :=
  (by positivity : (0 : ℝ) ≤ 1 / (T : ℝ) ^ 2).trans (le_max_left _ _)

/-- Positive source updates at a fixed late terminal, with the large-T premise
used by the printed early-weight proof explicitly retained. -/
theorem tdRateWeight_le_terminalEnvelope (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ)
    (hT : 2 ≤ T) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hcprod : c₁ * c₂ ≤ 1 / 8)
    (hlarge : Real.log (T : ℝ) ^ 2 ≤ c₁ * (1 - γ) * T)
    (hs : TDStepSizeSchedule γ c₁ c₂ T η)
    (t : ℕ) (htT : t ≤ T)
    (htime : (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ t)
    (k : ℕ) (_hk : 1 ≤ k) (hkt : k ≤ t) :
    tdRateWeight γ η t k ≤ tdTerminalWeightEnvelope γ T := by
  have hb := tdRateWeight_corrected_step_size γ c₁ c₂ T η hT hγ hγ1 hc₁ hc₂ hcprod
    hlarge hs t k htT hkt htime
  by_cases he : 2 * k ≤ t
  · exact (hb.1 he).trans (le_max_left _ _)
  · exact ((hb.2 (by omega)).1.trans (hb.2 (by omega)).2).trans (le_max_right _ _)

/-- A sufficient condition for the final terminal t=T to be late is c₂ log T≥1. This is separate
from the large-T contraction condition; neither is silently inferred. -/
theorem td_final_terminal_is_late (c₂ : ℝ) (T : ℕ)
    (hT : 2 ≤ T) (hc₂ : 0 < c₂) (hlate : 1 ≤ c₂ * Real.log (T : ℝ)) :
    (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ T := by
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  apply (div_le_iff₀ (mul_pos hc₂ hlog)).2
  exact le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ T) hlate

/-- A sufficient universal-constant relation makes the source late interval
nonempty, from the normalized consequence of its sample budget. -/
theorem td_normalizedBudget_implies_final_late (γ c₂ c₃ : ℝ) (T : ℕ)
    (hT : 2 ≤ T) (hγ : 0 ≤ γ) (_hγ1 : γ < 1) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hconstants : Real.exp (1 / c₂) ≤ c₃ * Real.log 2 ^ 4)
    (hnormalized : c₃ * Real.log (T : ℝ) ^ 4 ≤ (T : ℝ) * (1 - γ)) :
    1 ≤ c₂ * Real.log (T : ℝ) := by
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlogT : Real.log 2 ≤ Real.log (T : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hp : Real.log 2 ^ 4 ≤ Real.log (T : ℝ) ^ 4 :=
    pow_le_pow_left₀ hlog2 hlogT 4
  have hexpT : Real.exp (1 / c₂) ≤ (T : ℝ) := calc
    _ ≤ c₃ * Real.log 2 ^ 4 := hconstants
    _ ≤ c₃ * Real.log (T : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hp hc₃.le
    _ ≤ (T : ℝ) * (1 - γ) := hnormalized
    _ ≤ T := by nlinarith [show (0 : ℝ) ≤ T by positivity]
  have hl := Real.log_le_log (Real.exp_pos _) hexpT
  rw [Real.log_exp] at hl
  have hh := mul_le_mul_of_nonneg_left hl hc₂.le
  have he : c₂ * (1 / c₂) = 1 := by field_simp
  rwa [he] at hh

/-- The printed main budget implies the normalized scalar bound without using
an unproved late-terminal condition. This is weaker than the source accuracy
conclusion and contains no stochastic premise. -/
theorem td_mainBudget_implies_normalized (c₃ γ δ ε : ℝ) (S T : ℕ)
    (hc₃ : 0 < c₃) (hS : 1 ≤ S) (hT : 2 ≤ T) (hγ : γ < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hεmax : ε ≤ 1 / (1 - γ))
    (hbudget : c₃ * Real.log (T : ℝ) ^ 3 * Real.log ((S : ℝ) * T / δ) /
      ((1 - γ) ^ 3 * ε ^ 2) ≤ T) :
    c₃ * Real.log (T : ℝ) ^ 4 ≤ (T : ℝ) * (1 - γ) := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hgap : 0 < 1 - γ := sub_pos.mpr hγ
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hratio : (T : ℝ) ≤ (S : ℝ) * T / δ := by
    apply (le_div_iff₀ hδ).2
    have h1 := mul_le_mul_of_nonneg_left hδ1.le hTr.le
    have h2 := mul_le_mul_of_nonneg_right hSr hTr.le
    nlinarith
  have hl := Real.log_le_log hTr hratio
  have heps := (le_div_iff₀ hgap).mp hεmax
  have hepsSq : ε ^ 2 * (1 - γ) ^ 2 ≤ 1 := by
    have hh := (sq_le_sq₀ (mul_nonneg hε.le hgap.le) (by norm_num : (0 : ℝ) ≤ 1)).2 heps
    simpa only [mul_pow, one_pow] using hh
  have hb := (div_le_iff₀ (by positivity : 0 < (1 - γ) ^ 3 * ε ^ 2)).mp hbudget
  have hu := mul_le_mul_of_nonneg_left hepsSq (mul_nonneg hTr.le hgap.le)
  have hv := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ c₃ * Real.log (T : ℝ) ^ 3)
  nlinarith

end StatisticalRL.TemporalDifference

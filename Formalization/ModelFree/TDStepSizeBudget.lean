import Formalization.ModelFree.TDStepSizeLate

/-! The printed TD main sample budget discharges the explicit large-T premise
of the corrected step-size helper. This is deterministic scalar arithmetic,
not a proof of the stochastic TD accuracy theorem. -/
namespace StatisticalRL.TemporalDifference

/-- An explicit sufficient relation between the source's universal constants.
The witness depends only on c₁, not on the model, confidence or accuracy. -/
theorem exists_td_budget_constant (c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ 1 ≤ c₁ * c₃ * Real.log 2 ^ 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / (c₁ * Real.log 2 ^ 2), by positivity, ?_⟩
  have he : c₁ * (1 / (c₁ * Real.log 2 ^ 2)) * Real.log 2 ^ 2 = 1 := by
    field_simp
  exact he.ge

/-- Main theorem sample-budget consumption, retaining all logarithm and
accuracy domains. The large-T conclusion is proved, not a new premise. -/
theorem td_mainBudget_implies_large (c₁ c₃ γ δ ε : ℝ) (S T : ℕ)
    (hc₁ : 0 < c₁) (hc₃ : 0 < c₃) (hconstants : 1 ≤ c₁ * c₃ * Real.log 2 ^ 2)
    (hS : 1 ≤ S) (hT : 2 ≤ T) (hγ : γ < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hεmax : ε ≤ 1 / (1 - γ))
    (hbudget : c₃ * Real.log (T : ℝ) ^ 3 * Real.log ((S : ℝ) * T / δ) /
      ((1 - γ) ^ 3 * ε ^ 2) ≤ T) :
    Real.log (T : ℝ) ^ 2 ≤ c₁ * (1 - γ) * T := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hgap : 0 < 1 - γ := sub_pos.mpr hγ
  have hlogT : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2T : Real.log 2 ≤ Real.log (T : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hratio : (T : ℝ) ≤ (S : ℝ) * T / δ := by
    apply (le_div_iff₀ hδ).2
    have h1 := mul_le_mul_of_nonneg_left hδ1.le hTr.le
    have h2 := mul_le_mul_of_nonneg_right hSr hTr.le
    nlinarith
  have hlogRatio : Real.log (T : ℝ) ≤ Real.log ((S : ℝ) * T / δ) := Real.log_le_log hTr hratio
  have heps : ε * (1 - γ) ≤ 1 := (le_div_iff₀ hgap).mp hεmax
  have hepsSq : ε ^ 2 * (1 - γ) ^ 2 ≤ 1 := by
    have hh := (sq_le_sq₀ (mul_nonneg hε.le hgap.le) (by norm_num : (0 : ℝ) ≤ 1)).2 heps
    simpa only [mul_pow, one_pow] using hh
  have hden : 0 < (1 - γ) ^ 3 * ε ^ 2 := by positivity
  have hb := (div_le_iff₀ hden).mp hbudget
  have hupper := mul_le_mul_of_nonneg_left hepsSq (mul_nonneg hTr.le hgap.le)
  have hlower := mul_le_mul_of_nonneg_left hlogRatio (by positivity : 0 ≤ c₃ * Real.log (T : ℝ) ^ 3)
  have hnormalized : c₃ * Real.log (T : ℝ) ^ 4 ≤ (T : ℝ) * (1 - γ) := by nlinarith
  have hlogsq : Real.log 2 ^ 2 ≤ Real.log (T : ℝ) ^ 2 := (sq_le_sq₀ hlog2.le hlogT.le).2 hlog2T
  have hconstT : 1 ≤ c₁ * c₃ * Real.log (T : ℝ) ^ 2 :=
    hconstants.trans (mul_le_mul_of_nonneg_left hlogsq (mul_nonneg hc₁.le hc₃.le))
  have hscale := mul_le_mul_of_nonneg_right hconstT (sq_nonneg (Real.log (T : ℝ)))
  have hmain := mul_le_mul_of_nonneg_left hnormalized hc₁.le
  nlinarith

/-- Both source weight estimates under the actual main-theorem sample budget.
No separate large-T contraction premise remains on this declaration. -/
theorem tdRateWeight_step_size_of_mainBudget (γ c₁ c₂ c₃ δ ε : ℝ) (S T : ℕ) (η : ℕ → ℝ)
    (hS : 1 ≤ S) (hT : 2 ≤ T) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hcprod : c₁ * c₂ ≤ 1 / 8) (hconstants : 1 ≤ c₁ * c₃ * Real.log 2 ^ 2)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hεmax : ε ≤ 1 / (1 - γ))
    (hs : TDStepSizeSchedule γ c₁ c₂ T η)
    (hbudget : c₃ * Real.log (T : ℝ) ^ 3 * Real.log ((S : ℝ) * T / δ) /
      ((1 - γ) ^ 3 * ε ^ 2) ≤ T)
    (t k : ℕ) (htT : t ≤ T) (hkt : k ≤ t)
    (htime : (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ t) :
    (2 * k ≤ t → tdRateWeight γ η t k ≤ 1 / (T : ℝ) ^ 2) ∧
      (t < 2 * k → tdRateWeight γ η t k ≤ η k ∧
        η k ≤ 2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T)) := by
  exact tdRateWeight_corrected_step_size γ c₁ c₂ T η hT hγ hγ1 hc₁ hc₂ hcprod
    (td_mainBudget_implies_large c₁ c₃ γ δ ε S T hc₁ hc₃ hconstants hS hT hγ1
      hδ hδ1 hε hεmax hbudget) hs t k htT hkt htime

end StatisticalRL.TemporalDifference

import Formalization.ModelFree.TDLearningWeights
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Corrected standalone early TD weight bound. The large-T contraction premise
used in the source proof and the finite t≤T scope are explicit, not concealed. -/
namespace StatisticalRL.TemporalDifference

/-- Source finite-prefix schedule. No rate beyond T or condition on η0 occurs. -/
def TDStepSizeSchedule (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ T →
    1 / (1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 2) ≤ η i ∧
    η i ≤ 1 / (1 + c₂ * (1 - γ) * i / Real.log (T : ℝ) ^ 2)

/-- The lower schedule yields a real contraction lower bound only after the
explicit large-T condition from source line 2309 has been supplied. -/
theorem td_schedule_contraction_lower (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ)
    (hT : 2 ≤ T) (hγ : γ < 1) (hc₁ : 0 < c₁)
    (hlarge : Real.log (T : ℝ) ^ 2 ≤ c₁ * (1 - γ) * T)
    (hs : TDStepSizeSchedule γ c₁ c₂ T η) (i : ℕ) (hi : 1 ≤ i) (hiT : i ≤ T) :
    Real.log (T : ℝ) ^ 2 / (2 * c₁ * T) ≤ η i * (1 - γ) := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hlog2 : 0 < Real.log (T : ℝ) ^ 2 := sq_pos_of_pos hlog
  have hgap : 0 < 1 - γ := sub_pos.mpr hγ
  have hden : 0 < 1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 2 := by positivity
  have hη := (hs i hi hiT).1
  have hη0 : 0 ≤ η i := (le_of_lt (one_div_pos.mpr hden)).trans hη
  have hx := (div_le_iff₀ hden).mp hη
  have hx' := mul_le_mul_of_nonneg_right hx hlog2.le
  have he : (η i * (1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 2)) *
      Real.log (T : ℝ) ^ 2 = η i * (Real.log (T : ℝ) ^ 2 + c₁ * (1 - γ) * T) := by
    field_simp
  rw [he, one_mul] at hx'
  have hb := mul_le_mul_of_nonneg_left hlarge hη0
  apply (div_le_iff₀ (by positivity : 0 < 2 * c₁ * (T : ℝ))).2
  nlinarith

/-- The source schedule implies the required finite rate interval [0,1]. -/
theorem td_schedule_rate_bounds (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ)
    (hT : 2 ≤ T) (hγ : γ < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hs : TDStepSizeSchedule γ c₁ c₂ T η) (i : ℕ) (hi : 1 ≤ i) (hiT : i ≤ T) :
    0 ≤ η i ∧ η i ≤ 1 := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hgap : 0 < 1 - γ := sub_pos.mpr hγ
  have hiR : 0 < (i : ℝ) := by exact_mod_cast hi
  have hden₁ : 0 < 1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 2 := by positivity
  have hden₂ : 1 ≤ 1 + c₂ * (1 - γ) * i / Real.log (T : ℝ) ^ 2 := by
    have hh : 0 ≤ c₂ * (1 - γ) * i / Real.log (T : ℝ) ^ 2 := by positivity
    linarith
  refine ⟨(le_of_lt (one_div_pos.mpr hden₁)).trans (hs i hi hiT).1, ?_⟩
  exact (hs i hi hiT).2.trans ((div_le_iff₀ (by linarith : 0 <
    1 + c₂ * (1 - γ) * i / Real.log (T : ℝ) ^ 2)).2 (by linarith))

/-- Corrected early-weight estimate: the additional large-T condition and
finite schedule/time domains are explicit. No main TD theorem is asserted. -/
theorem tdRateWeight_early_le_inv_sq (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ)
    (hT : 2 ≤ T) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hcprod : c₁ * c₂ ≤ 1 / 8)
    (hlarge : Real.log (T : ℝ) ^ 2 ≤ c₁ * (1 - γ) * T)
    (hs : TDStepSizeSchedule γ c₁ c₂ T η)
    (t k : ℕ) (htT : t ≤ T)
    (htime : (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ t)
    (hk : 2 * k ≤ t) : tdRateWeight γ η t k ≤ 1 / (T : ℝ) ^ 2 := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  let α := Real.log (T : ℝ) ^ 2 / (2 * c₁ * T)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hkt : k ≤ t := by omega
  have hp := tdRateWeight_le_exp γ η t k α hγ hγ1.le hkt
    (fun i hi hit ↦ td_schedule_rate_bounds γ c₁ c₂ T η hT hγ1 hc₁ hc₂ hs i hi (hit.trans htT))
    (fun i hki hit ↦ td_schedule_contraction_lower γ c₁ c₂ T η hT hγ1 hc₁ hlarge hs i
      (by omega) (hit.trans htT))
  have hhalf : (t : ℝ) / 2 ≤ (t - k : ℕ) := by
    have hh : 2 * (k : ℝ) ≤ t := by exact_mod_cast hk
    rw [Nat.cast_sub hkt]
    linarith
  have htime' : (T : ℝ) ≤ t * (c₂ * Real.log (T : ℝ)) :=
    (div_le_iff₀ (mul_pos hc₂ hlog)).mp htime
  have hmain : 2 * Real.log (T : ℝ) ≤ α * ((t : ℝ) / 2) := by
    dsimp [α]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * c₁ * (T : ℝ))).2
    have hh := mul_le_mul_of_nonneg_left htime' (by positivity : 0 ≤ 8 * c₁ * Real.log (T : ℝ))
    have hc := mul_le_mul_of_nonneg_right hcprod (by positivity : 0 ≤ 8 * (t : ℝ) * Real.log (T : ℝ) ^ 2)
    nlinarith
  have hexp : Real.exp (-α * (t - k : ℕ)) ≤ Real.exp (-(2 * Real.log (T : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hhalf hα
    linarith
  have he : Real.exp (-(2 * Real.log (T : ℝ))) = 1 / (T : ℝ) ^ 2 := by
    rw [Real.exp_neg, show 2 * Real.log (T : ℝ) = Real.log (T : ℝ) + Real.log (T : ℝ) by ring,
      Real.exp_add, Real.exp_log hTr]
    simp [pow_two]
  exact hp.trans (hexp.trans_eq he)

end StatisticalRL.TemporalDifference

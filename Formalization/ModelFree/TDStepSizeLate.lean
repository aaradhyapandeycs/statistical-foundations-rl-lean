import Formalization.ModelFree.TDStepSizeEarly

/-! Late TD learning-rate weight bound from the actual finite source schedule.
Unlike the early estimate, no large-T contraction premise is used. -/
namespace StatisticalRL.TemporalDifference

/-- Source late-weight estimate, preserving the exact 2 log³T/((1−γ)T)
constant and explicit finite time domain. -/
theorem tdRateWeight_late_bounds (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ)
    (hT : 2 ≤ T) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hs : TDStepSizeSchedule γ c₁ c₂ T η)
    (t k : ℕ) (htT : t ≤ T) (hkt : k ≤ t)
    (htime : (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ t) (hk : t < 2 * k) :
    tdRateWeight γ η t k ≤ η k ∧
      η k ≤ 2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T) := by
  have hk0 : 0 < k := by omega
  have hkT : k ≤ T := hkt.trans htT
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk0
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hgap : 0 < 1 - γ := sub_pos.mpr hγ1
  constructor
  · exact tdRateWeight_le_rate γ η t k hγ hγ1.le hk0 hkt
      (fun i hi hit ↦ td_schedule_rate_bounds γ c₁ c₂ T η hT hγ1 hc₁ hc₂ hs i hi (hit.trans htT))
  · have hD : 0 < c₂ * (1 - γ) * (k : ℝ) := by positivity
    have hx : 0 < c₂ * (1 - γ) * (k : ℝ) / Real.log (T : ℝ) ^ 2 := by positivity
    have hrecip : 1 / (1 + c₂ * (1 - γ) * (k : ℝ) / Real.log (T : ℝ) ^ 2) ≤
        1 / (c₂ * (1 - γ) * (k : ℝ) / Real.log (T : ℝ) ^ 2) :=
      one_div_le_one_div_of_le hx (by linarith)
    have hrate : η k ≤ Real.log (T : ℝ) ^ 2 / (c₂ * (1 - γ) * (k : ℝ)) := by
      have hh := (hs k hk0 hkT).2.trans hrecip
      simpa only [one_div_div] using hh
    have htime' : (T : ℝ) ≤ t * (c₂ * Real.log (T : ℝ)) :=
      (div_le_iff₀ (mul_pos hc₂ hlog)).mp htime
    have hk' : (t : ℝ) < 2 * (k : ℝ) := by exact_mod_cast hk
    have hmul := mul_lt_mul_of_pos_right hk' (mul_pos hc₂ hlog)
    have hcount : (T : ℝ) ≤ 2 * c₂ * (k : ℝ) * Real.log (T : ℝ) := by linarith
    have hweighted := mul_le_mul_of_nonneg_left hcount
      (by positivity : 0 ≤ (1 - γ) * Real.log (T : ℝ) ^ 2)
    apply hrate.trans
    apply (div_le_div_iff₀ hD (mul_pos hgap hTr)).2
    nlinarith

/-- Both cases of the corrected standalone TD step-size estimate. The extra
large-T condition is retained explicitly because the printed proof needs it. -/
theorem tdRateWeight_corrected_step_size (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ)
    (hT : 2 ≤ T) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hcprod : c₁ * c₂ ≤ 1 / 8)
    (hlarge : Real.log (T : ℝ) ^ 2 ≤ c₁ * (1 - γ) * T)
    (hs : TDStepSizeSchedule γ c₁ c₂ T η)
    (t k : ℕ) (htT : t ≤ T) (hkt : k ≤ t)
    (htime : (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ t) :
    (2 * k ≤ t → tdRateWeight γ η t k ≤ 1 / (T : ℝ) ^ 2) ∧
      (t < 2 * k → tdRateWeight γ η t k ≤ η k ∧
        η k ≤ 2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T)) := by
  exact ⟨fun hk ↦ tdRateWeight_early_le_inv_sq γ c₁ c₂ T η hT hγ hγ1 hc₁ hc₂ hcprod
      hlarge hs t k htT htime hk,
    fun hk ↦ tdRateWeight_late_bounds γ c₁ c₂ T η hT hγ hγ1 hc₁ hc₂ hs t k htT hkt htime hk⟩

end StatisticalRL.TemporalDifference

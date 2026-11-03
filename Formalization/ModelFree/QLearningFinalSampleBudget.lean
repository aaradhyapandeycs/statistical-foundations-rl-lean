import Formalization.ModelFree.QLearningFinalRateArithmetic

/-! exact source sample budget to normalized scalar
and rho bounds. No target Q accuracy or comparator stability is a premise. -/
namespace StatisticalRL.QLearning

/-- The source cardinality/confidence domain gives R=SAT/delta>=T. -/
theorem qFinal_sample_ratio_ge_T (S A T : ℕ) (δ : ℝ)
    (hS : 1 ≤ S) (hA : 1 ≤ A) (hT : 2 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (T : ℝ) ≤ (S : ℝ)*A*T/δ := by
  have hSr : (1:ℝ) ≤ S := by exact_mod_cast hS
  have hAr : (1:ℝ) ≤ A := by exact_mod_cast hA
  have hTr : 0 ≤ (T:ℝ) := by positivity
  have hSA : (1:ℝ) ≤ (S:ℝ)*A := by nlinarith
  apply (le_div_iff₀ hδ).2
  have h1 := mul_le_mul_of_nonneg_left hδ1.le hTr
  have h2 := mul_le_mul_of_nonneg_right hSA hTr
  nlinarith

/-- Actual source budget and epsilon<=H imply c3 log^5T<=T h^2. -/
theorem qFinal_budget_normalized (γ c₃ δ ε : ℝ) (S A T : ℕ)
    (hc₃ : 0 < c₃) (hγ : γ < 1) (hS : 1 ≤ S) (hA : 1 ≤ A) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hεmax : ε ≤ 1/(1-γ))
    (hbudget : c₃*Real.log (T:ℝ)^4*Real.log ((S:ℝ)*A*T/δ)/((1-γ)^4*ε^2) ≤ T) :
    c₃*Real.log (T:ℝ)^5 ≤ (T:ℝ)*(1-γ)^2 := by
  have hgap : 0 < 1-γ := sub_pos.mpr hγ
  have hTr : 0 < (T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hlog : 0 < Real.log (T:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<T))
  have hl := Real.log_le_log hTr (qFinal_sample_ratio_ge_T S A T δ hS hA hT hδ hδ1)
  have heps := (le_div_iff₀ hgap).mp hεmax
  have hs : ε^2*(1-γ)^2 ≤ 1 := by
    have hh := (sq_le_sq₀ (mul_nonneg hε.le hgap.le) (by norm_num : (0:ℝ)≤1)).2 heps
    simpa only [mul_pow, one_pow] using hh
  have hb := (div_le_iff₀ (by positivity : 0 < (1-γ)^4*ε^2)).mp hbudget
  have hu := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (T:ℝ)*(1-γ)^2)
  have hd := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ c₃*Real.log (T:ℝ)^4)
  nlinarith

/-- Exact rho formula before consuming the sample budget. -/
theorem qFinal_sourceRho_prebudget (γ c₂ δ : ℝ) (S A T : ℕ)
    (hγ : γ < 1) (hc₂ : 0 < c₂) (hS : 1 ≤ S) (hA : 1 ≤ A) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    qChiSourceRadius (qChiSourceRateEnvelope γ c₂ T) δ S A T ≤
      48*Real.log (T:ℝ)^3*Real.log ((S:ℝ)*A*T/δ)/(c₂*(1-γ)*T) := by
  let R := (S:ℝ)*A*T/δ
  have hTr : 0 < (T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hlog : 0 < Real.log (T:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<T))
  have hgap : 0 < 1-γ := sub_pos.mpr hγ
  have hR : 2 ≤ R := (by exact_mod_cast hT : (2:ℝ) ≤ T).trans
    (qFinal_sample_ratio_ge_T S A T δ hS hA hT hδ hδ1)
  have hlog4 : 0 ≤ Real.log (4*R) := (Real.log_pos (by linarith)).le
  have hcompare := qFinal_log_four_mul_le R hR
  have hη := min_le_right (1:ℝ) (2*Real.log (T:ℝ)^3/(c₂*(1-γ)*T))
  have he : 4*(S:ℝ)*A*T/δ = 4*R := by dsimp [R]; ring
  unfold qChiSourceRadius qChiSourceRateEnvelope
  rw [he]
  calc
    _ ≤ 8*(2*Real.log (T:ℝ)^3/(c₂*(1-γ)*T))*Real.log (4*R) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη (by norm_num)) hlog4
    _ ≤ 8*(2*Real.log (T:ℝ)^3/(c₂*(1-γ)*T))*(3*Real.log R) :=
      mul_le_mul_of_nonneg_left hcompare (by positivity)
    _ = _ := by dsimp [R]; ring

/-- The exact printed sample budget gives the source rho budget, with no
rho estimate or target error hypothesis added to the actual theorem. -/
theorem qFinal_sourceRho_budget (γ c₂ c₃ δ ε : ℝ) (S A T : ℕ)
    (hγ : γ < 1) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hS : 1 ≤ S) (hA : 1 ≤ A) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε)
    (hbudget : c₃*Real.log (T:ℝ)^4*Real.log ((S:ℝ)*A*T/δ)/((1-γ)^4*ε^2) ≤ T) :
    qChiSourceRadius (qChiSourceRateEnvelope γ c₂ T) δ S A T ≤
      48*ε^2*(1-γ)^3/(c₂*c₃*Real.log (T:ℝ)) := by
  let ρ := qChiSourceRadius (qChiSourceRateEnvelope γ c₂ T) δ S A T
  have hgap : 0 < 1-γ := sub_pos.mpr hγ
  have hTr : 0 < (T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hlog : 0 < Real.log (T:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<T))
  have hp := qFinal_sourceRho_prebudget γ c₂ δ S A T hγ hc₂ hS hA hT hδ hδ1
  have hp' : ρ*(c₂*(1-γ)*T) ≤ 48*Real.log (T:ℝ)^3*Real.log ((S:ℝ)*A*T/δ) :=
    (le_div_iff₀ (by positivity : 0 < c₂*(1-γ)*T)).mp hp
  have hb := (div_le_iff₀ (by positivity : 0 < (1-γ)^4*ε^2)).mp hbudget
  have hm := mul_le_mul_of_nonneg_right hp' (by positivity : 0 ≤ c₃*Real.log (T:ℝ))
  have hb' := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤48)
  apply (le_div_iff₀ (by positivity : 0 < c₂*c₃*Real.log (T:ℝ))).2
  apply (mul_le_mul_iff_left₀ (show 0 < (1-γ)*(T:ℝ) by positivity)).mp
  nlinarith

end StatisticalRL.QLearning

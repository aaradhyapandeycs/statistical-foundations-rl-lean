import Formalization.ModelFree.QLearningFinalSampleBudget
import Formalization.ModelFree.QLearningLateRateSchedule

/-! source budget regularity, transient scale, and
actual schedule-product decay. No final error or decay estimate is assumed. -/
open scoped BigOperators
namespace StatisticalRL.QLearning

theorem qFinal_normalized_regularities (h c₃ T : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hc₃ : 0 < c₃) (hT : 2 ≤ T)
    (hexp : Real.exp 4 ≤ c₃ * Real.log 2 ^ 5)
    (hconst : 1 ≤ c₃ * Real.log 2 ^ 2)
    (hn : c₃ * Real.log T ^ 5 ≤ T * h ^ 2) :
    4 ≤ Real.log T ∧ Real.log T ^ 3 ≤ h*T := by
  have hTp : 0 < T := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlp : 0 < Real.log T := hl2.trans_le hl
  have hp5 := pow_le_pow_left₀ hl2.le hl 5
  have hp2 := pow_le_pow_left₀ hl2.le hl 2
  have hhsq : h^2 ≤ 1 := by nlinarith
  have hhh : h^2 ≤ h := by nlinarith
  have hexpT : Real.exp 4 ≤ T := calc
    _ ≤ c₃ * Real.log 2 ^ 5 := hexp
    _ ≤ c₃ * Real.log T ^ 5 := mul_le_mul_of_nonneg_left hp5 hc₃.le
    _ ≤ T*h^2 := hn
    _ ≤ T := by nlinarith
  have hlog4 := Real.log_le_log (Real.exp_pos 4) hexpT
  rw [Real.log_exp] at hlog4
  have hcT : 1 ≤ c₃ * Real.log T ^ 2 :=
    hconst.trans (mul_le_mul_of_nonneg_left hp2 hc₃.le)
  have hscale := mul_le_mul_of_nonneg_right hcT (pow_nonneg hlp.le 3)
  constructor
  · exact hlog4
  · nlinarith

/-- The full source budget, rather than a new lower-accuracy premise, supplies
the elementary transient scale epsilon*h*T>=1. -/
theorem qFinal_budget_transient (γ c₃ δ ε : ℝ) (S A T : ℕ)
    (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hc₃ : 0 < c₃)
    (hS : 1 ≤ S) (hA : 1 ≤ A) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε)
    (hconstant : 1 ≤ c₃ * Real.log 2 ^ 5)
    (hbudget : c₃*Real.log (T:ℝ)^4*Real.log ((S:ℝ)*A*T/δ)/((1-γ)^4*ε^2) ≤ T) :
    1 ≤ ε*(1-γ)*T := by
  have hgap : 0 < 1-γ := sub_pos.mpr hγ
  have hgap1 : 1-γ ≤ 1 := by linarith
  have hTr : (2:ℝ) ≤ T := by exact_mod_cast hT
  have hTp : 0 < (T:ℝ) := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log (T:ℝ) := Real.log_le_log (by norm_num) hTr
  have hLp : 0 < Real.log (T:ℝ) := hl2.trans_le hl
  have hR := Real.log_le_log hTp (qFinal_sample_ratio_ge_T S A T δ hS hA hT hδ hδ1)
  have hmin : 1 ≤ c₃*Real.log (T:ℝ)^5 := hconstant.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl2.le hl 5) hc₃.le)
  have hlower := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ c₃*Real.log (T:ℝ)^4)
  have hb := (div_le_iff₀ (by positivity : 0 < (1-γ)^4*ε^2)).mp hbudget
  have hone : 1 ≤ (T:ℝ)*(1-γ)^4*ε^2 := by nlinarith
  have hhsq : (1-γ)^2 ≤ 1 := by nlinarith
  have hdiff : 0 ≤ (T:ℝ) - (1-γ)^2 := by linarith
  have hm := mul_nonneg (show 0 ≤ ε^2*(1-γ)^2*(T:ℝ) by positivity) hdiff
  have hX : 0 ≤ ε*(1-γ)*T := by positivity
  nlinarith

/-- Exact source lower schedule to the late-step loss bound, under proved
regularity log^3T<=hT and the source small constant c1<=1. -/
theorem qFinal_schedule_rate_lower (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ)
    (hγ : γ < 1) (hc₁ : 0 < c₁) (hc₁1 : c₁ ≤ 1) (hc₂ : 0 < c₂)
    (hT : 2 ≤ T) (hs : qSourceRateSchedule γ c₁ c₂ T η)
    (hlarge : Real.log (T:ℝ)^3 ≤ (1-γ)*T) (i : ℕ) (hiT : i ≤ T) :
    Real.log (T:ℝ)^3/(2*(1-γ)*T) ≤ η i := by
  have hgap : 0 < 1-γ := sub_pos.mpr hγ
  have hTr : 0 < (T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hlog : 0 < Real.log (T:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<T))
  have hη0 := (qSourceRate_unit_interval γ c₁ c₂ T η hT hγ hc₁ hc₂ hs i hiT).1
  have hd : 0 < 1+c₁*(1-γ)*T/Real.log (T:ℝ)^3 := by positivity
  have hb := (div_le_iff₀ hd).mp (hs i hiT).1
  have hm := mul_le_mul_of_nonneg_right hb (pow_nonneg hlog.le 3)
  have he : (η i * (1+c₁*(1-γ)*T/Real.log (T:ℝ)^3))*Real.log (T:ℝ)^3 =
      η i * (Real.log (T:ℝ)^3+c₁*(1-γ)*T) := by field_simp
  rw [he, one_mul] at hm
  have hc := mul_le_mul_of_nonneg_right hc₁1 (by positivity : 0 ≤ (1-γ)*(T:ℝ))
  have hu := mul_le_mul_of_nonneg_left (show Real.log (T:ℝ)^3+c₁*(1-γ)*T ≤ 2*(1-γ)*T by nlinarith) hη0
  apply (div_le_iff₀ (by positivity : 0 < 2*(1-γ)*(T:ℝ))).2
  nlinarith

/-- Actual source schedule gives the source T^-4 late product; log/large-time
conditions are explicit intermediate consequences of the budget. -/
theorem qFinal_schedule_product_decay (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ)
    (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hc₁ : 0 < c₁) (hc₁1 : c₁ ≤ 1) (hc₂ : 0 < c₂)
    (hT : 2 ≤ T) (hs : qSourceRateSchedule γ c₁ c₂ T η)
    (hlog4 : 4 ≤ Real.log (T:ℝ)) (hlarge : Real.log (T:ℝ)^3 ≤ (1-γ)*T) :
    (∏ i ∈ Finset.Icc (T/2+1) T, (1-η i*(1-γ))) ≤ 1/(T:ℝ)^4 := by
  have hgap : 0 < 1-γ := sub_pos.mpr hγ
  have hTr : 0 < (T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hlog : 0 < Real.log (T:ℝ) := by linarith
  let S := Finset.Icc (T/2+1) T
  let α := Real.log (T:ℝ)^3/(2*(T:ℝ))
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hfactor (i : ℕ) (hi : i∈S) :
      0 ≤ 1-η i*(1-γ) ∧ 1-η i*(1-γ) ≤ Real.exp (-α) := by
    have hi' := Finset.mem_Icc.mp hi
    have hη := qSourceRate_unit_interval γ c₁ c₂ T η hT hγ hc₁ hc₂ hs i hi'.2
    have hl := qFinal_schedule_rate_lower γ c₁ c₂ T η hγ hc₁ hc₁1 hc₂ hT hs hlarge i hi'.2
    have hmul := mul_le_mul_of_nonneg_right hl hgap.le
    have hloss : α ≤ η i*(1-γ) := by
      dsimp [α]
      have he : (Real.log (T:ℝ)^3/(2*(1-γ)*T))*(1-γ) = Real.log (T:ℝ)^3/(2*T) := by field_simp
      rwa [he] at hmul
    constructor
    · nlinarith
    · exact (Real.one_sub_le_exp_neg (η i*(1-γ))).trans (Real.exp_le_exp.mpr (by linarith))
  have hprod : (∏ i ∈ S, (1-η i*(1-γ))) ≤ (Real.exp (-α))^S.card := by
    calc
      _ ≤ ∏ _i ∈ S, Real.exp (-α) := Finset.prod_le_prod (fun i hi ↦ (hfactor i hi).1) (fun i hi ↦ (hfactor i hi).2)
      _ = _ := by simp
  have hcNat : S.card = T-T/2 := by dsimp [S]; rw [Nat.card_Icc]; omega
  have hc : (T:ℝ)/2 ≤ S.card := by
    have hn : T ≤ 2*(T-T/2) := by omega
    have hr : (T:ℝ) ≤ 2*(S.card:ℝ) := by rw [hcNat]; exact_mod_cast hn
    linarith
  have hcount := mul_le_mul_of_nonneg_left hc hα
  have hαT : α*((T:ℝ)/2) = Real.log (T:ℝ)^3/4 := by dsimp [α]; field_simp; ring
  rw [hαT] at hcount
  have hlogcube : 4*Real.log (T:ℝ) ≤ Real.log (T:ℝ)^3/4 := by nlinarith [sq_nonneg (Real.log (T:ℝ)-4)]
  have hexp : (Real.exp (-α))^S.card ≤ Real.exp (-(4*Real.log (T:ℝ))) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  have he : Real.exp (-(4*Real.log (T:ℝ))) = 1/(T:ℝ)^4 := by
    have hfour : Real.exp (4*Real.log (T:ℝ)) = Real.exp (Real.log (T:ℝ))^4 := by
      simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (Real.log (T:ℝ)) 4
    rw [Real.exp_neg, hfour, Real.exp_log hTr]
    simp only [one_div]
  exact hprod.trans (hexp.trans_eq he)

/-- The actual source budget discharges every intermediate decay/transient
premise used in the scalar final-radius helper. Universal constants remain
explicit and precede all model-domain uses. -/
theorem qFinal_source_budget_consequences (γ c₁ c₂ c₃ δ ε : ℝ) (S A T : ℕ) (η : ℕ → ℝ)
    (hγ0 : 0 ≤ γ) (hγ : γ < 1) (hc₁ : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hexp : Real.exp 4 ≤ c₃*Real.log 2^5) (hconst : 1 ≤ c₃*Real.log 2^2)
    (hden : 384 ≤ c₂*c₃*Real.log 2)
    (hS : 1 ≤ S) (hA : 1 ≤ A) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hεmax : ε ≤ 1/(1-γ))
    (hs : qSourceRateSchedule γ c₁ c₂ T η)
    (hbudget : c₃*Real.log (T:ℝ)^4*Real.log ((S:ℝ)*A*T/δ)/((1-γ)^4*ε^2) ≤ T) :
    (∏ i ∈ Finset.Icc (T/2+1) T, (1-η i*(1-γ))) ≤ 1/(T:ℝ)^4 ∧
      1 ≤ ε*(1-γ)*T ∧ 384 ≤ c₂*c₃*Real.log (T:ℝ) := by
  have hn := qFinal_budget_normalized γ c₃ δ ε S A T hc₃ hγ hS hA hT hδ hδ1 hε hεmax hbudget
  have hr := qFinal_normalized_regularities (1-γ) c₃ T (sub_pos.mpr hγ) (by linarith) hc₃
    (by exact_mod_cast hT) hexp hconst hn
  have hprod := qFinal_schedule_product_decay γ c₁ c₂ T η hγ0 hγ hc₁ hc₁1 hc₂ hT hs hr.1 hr.2
  have hone : 1 ≤ Real.exp (4:ℝ) := Real.one_le_exp (by norm_num)
  have ht := qFinal_budget_transient γ c₃ δ ε S A T hγ0 hγ hc₃ hS hA hT hδ hδ1 hε (hone.trans hexp) hbudget
  have hl : Real.log 2 ≤ Real.log (T:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hd := hden.trans (mul_le_mul_of_nonneg_left hl (mul_nonneg hc₂.le hc₃.le))
  exact ⟨hprod, ht, hd⟩

/-- Complete source sample-size conversion for the deterministic total
comparison radius. This remains a scalar result; actual comparator closeness
and its transfer to Q error must be supplied by their independently proved
source results, not inferred from this arithmetic. -/
theorem qFinal_source_scalar_radius_le (γ c₁ c₂ c₃ δ ε : ℝ) (S A T : ℕ) (η : ℕ → ℝ)
    (hγhalf : 1/2 ≤ γ) (hγ : γ < 1) (hc₁ : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hexp : Real.exp 4 ≤ c₃*Real.log 2^5) (hconst : 1 ≤ c₃*Real.log 2^2)
    (hden : 384 ≤ c₂*c₃*Real.log 2)
    (hS : 1 ≤ S) (hA : 1 ≤ A) (hT : 2 ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hεmax : ε ≤ 1/(1-γ))
    (hs : qSourceRateSchedule γ c₁ c₂ T η)
    (hbudget : c₃*Real.log (T:ℝ)^4*Real.log ((S:ℝ)*A*T/δ)/((1-γ)^4*ε^2) ≤ T) :
    let ρ := qChiSourceRadius (qChiSourceRateEnvelope γ c₂ T) δ S A T
    ((1+2*ρ+Real.sqrt ρ)/(1-γ)) * (∏ i ∈ Finset.Icc (T/2+1) T, (1-η i*(1-γ))) +
      Real.sqrt (γ*ρ/(2*(1-γ)^3)) + 2*ρ/(1-γ)^2 ≤ ε := by
  have hγ0 : 0 ≤ γ := by linarith
  have hc := qFinal_source_budget_consequences γ c₁ c₂ c₃ δ ε S A T η hγ0 hγ hc₁ hc₁1 hc₂ hc₃
    hexp hconst hden hS hA hT hδ hδ1 hε hεmax hs hbudget
  have hρ := (qChiSourceRadius_pos _ δ S A T
    (qChiSourceRateEnvelope_pos γ c₂ T hγ hc₂ hT) hδ hδ1 hS hA hT).le
  exact qFinal_scalar_radius_le γ (1-γ) ε _ (c₂*c₃*Real.log (T:ℝ)) _ T hγ0 hγ.le
    (sub_pos.mpr hγ) (by linarith) hε hεmax hρ hc.2.2
    (qFinal_sourceRho_budget γ c₂ c₃ δ ε S A T hγ hc₂ hc₃ hS hA hT hδ hδ1 hε hbudget)
    (by exact_mod_cast hT) hc.2.1 hc.1

end StatisticalRL.QLearning

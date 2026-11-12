import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # Arithmetic consequences of the sample-size budget of Theorem 4.12

Notation: `h = 1/(1-γ)`, `P = log T`, `ι = log(SAT/δ)`, `c₂ = max(e^{32/c₁}, 4096)`. The budget gives
`c₂ ι² h⁴ P³/ε² ≤ T μ_min` and `c₂ ι² h t̄ ≤ T μ_min`. -/

set_option linter.unusedSectionVars false

namespace StatisticalRL.AsyncQ

/-- The universal constant `c₂(c₁) = max(e^{32/c₁}, 4096)`. -/
noncomputable def asyncC₂ (c₁ : ℝ) : ℝ := max (Real.exp (32 / c₁)) 4096

/-- Standing arithmetic hypotheses (all derived from the theorem's premises). -/
structure ArithHyp (c₁ γ ε δ μm SA tb h P ι T : ℝ) : Prop where
  hc₁ : 0 < c₁
  hc₁1 : c₁ ≤ 1
  hγ : 1 / 2 ≤ γ
  hγ1 : γ < 1
  hε : 0 < ε
  hε1 : ε ≤ 1
  hδ : 0 < δ
  hδ1 : δ < 1
  hμ : 0 < μm
  hμ1 : μm ≤ 1
  hSA : 1 ≤ SA
  htb : 1 ≤ tb
  hT : 2 ≤ T
  hh : h = 1 / (1 - γ)
  hP : P = Real.log T
  hι : ι = Real.log (SA * T / δ)
  hA2 : asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P ^ 3 / ε ^ 2 ≤ T * μm
  hA3 : asyncC₂ c₁ * ι ^ 2 * h * tb ≤ T * μm

namespace ArithHyp

variable {c₁ γ ε δ μm SA tb h P ι T : ℝ} (H : ArithHyp c₁ γ ε δ μm SA tb h P ι T)
include H

theorem c₂_ge : 4096 ≤ asyncC₂ c₁ := le_max_right _ _

theorem c₂_ge_exp : Real.exp (32 / c₁) ≤ asyncC₂ c₁ := le_max_left _ _

theorem h_ge : 2 ≤ h := by
  rw [H.hh, le_div_iff₀ (by linarith [H.hγ1])]; linarith [H.hγ]

theorem h_mul : h * (1 - γ) = 1 := by
  rw [H.hh]; field_simp [show (1 - γ) ≠ 0 by linarith [H.hγ1]]

theorem T_pos : 0 < T := by linarith [H.hT]

theorem P_pos : 0 < P := by rw [H.hP]; exact Real.log_pos (by linarith [H.hT])

theorem P_ge_log2 : Real.log 2 ≤ P := by rw [H.hP]; exact Real.log_le_log (by norm_num) H.hT

theorem T_eq_exp : T = Real.exp P := by rw [H.hP, Real.exp_log H.T_pos]

theorem ι_ge_P : P ≤ ι := by
  rw [H.hP, H.hι]
  apply Real.log_le_log H.T_pos
  rw [le_div_iff₀ H.hδ]
  have := H.T_pos
  nlinarith [H.hSA, H.hδ1]

theorem ι_pos : 0 < ι := lt_of_lt_of_le H.P_pos H.ι_ge_P

/-- `T ≥ c₂ ι² h⁴ P³ / ε²`. -/
theorem T_ge_main : asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P ^ 3 / ε ^ 2 ≤ T :=
  H.hA2.trans (by have := H.T_pos; nlinarith [H.hμ1, H.hμ])

/-- `c₂ ι² h⁴ P³ ≤ c₂ ι² h⁴ P³ / ε²`. -/
theorem main_ge_noeps : asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P ^ 3 ≤
    asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P ^ 3 / ε ^ 2 := by
  have h0 : 0 ≤ asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P ^ 3 := by
    have := H.P_pos; have := H.c₂_ge; positivity
  exact le_div_self h0 (by have := H.hε; positivity) (by nlinarith [H.hε1, H.hε])

/-- (A1) `log T ≥ 32/c₁`. -/
theorem P_ge : 32 / c₁ ≤ P := by
  by_contra hlt
  push_neg at hlt
  have hT : T < asyncC₂ c₁ := by
    rw [H.T_eq_exp]; exact (Real.exp_lt_exp.mpr hlt).trans_le H.c₂_ge_exp
  have hl2 := Real.log_two_gt_d9
  have hP := H.P_ge_log2
  have hP0 := H.P_pos
  have hι := H.ι_ge_P
  have hh := H.h_ge
  have hc := H.c₂_ge
  have h1 : (1 : ℝ) ≤ 16 * P ^ 5 := by
    have : (0.6931471803 : ℝ) ^ 5 ≤ P ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
    norm_num at this; linarith
  have h2 : P ^ 2 ≤ ι ^ 2 := pow_le_pow_left₀ hP0.le hι 2
  have h3 : (16 : ℝ) ≤ h ^ 4 := by
    have : (2 : ℝ) ^ 4 ≤ h ^ 4 := pow_le_pow_left₀ (by norm_num) hh 4
    norm_num at this; linarith
  have h4 : asyncC₂ c₁ * (16 * P ^ 5) ≤ asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P ^ 3 := by
    have e : asyncC₂ c₁ * (16 * P ^ 5) = asyncC₂ c₁ * P ^ 2 * 16 * P ^ 3 := by ring
    rw [e]
    have hP3 : 0 ≤ P ^ 3 := by positivity
    have hc0 : 0 ≤ asyncC₂ c₁ := by linarith
    gcongr
  have := H.main_ge_noeps.trans H.T_ge_main
  nlinarith

theorem P_ge_32 : 32 ≤ P := by
  have := H.P_ge
  have : 32 ≤ 32 / c₁ := by rw [le_div_iff₀ H.hc₁]; nlinarith [H.hc₁1]
  linarith

theorem ι_ge_one : 1 ≤ ι := by linarith [H.ι_ge_P, H.P_ge_32]

/-- `T ≥ 4096 h⁴/ε²` (with all other budget factors ≥ 1). -/
theorem T_ge_h4 : 4096 * h ^ 4 / ε ^ 2 ≤ T := by
  refine le_trans ?_ H.T_ge_main
  have hι : 1 ≤ ι ^ 2 := by nlinarith [H.ι_ge_one]
  have hP : 1 ≤ P ^ 3 := one_le_pow₀ (by linarith [H.P_ge_32])
  have hc := H.c₂_ge
  have hε := H.hε
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh4 : 0 ≤ h ^ 4 := by positivity
  calc 4096 * h ^ 4 ≤ asyncC₂ c₁ * h ^ 4 := by nlinarith
    _ ≤ asyncC₂ c₁ * ι ^ 2 * h ^ 4 := by
        nlinarith [mul_le_mul_of_nonneg_left hι (show (0:ℝ) ≤ asyncC₂ c₁ * h ^ 4 by nlinarith)]
    _ ≤ asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P ^ 3 := by
        have : 0 ≤ asyncC₂ c₁ * ι ^ 2 * h ^ 4 :=
          mul_nonneg (mul_nonneg (by linarith) (by positivity)) hh4
        nlinarith

/-- `T ≥ 4096 h P`. -/
theorem T_ge_hP : 4096 * h * P ≤ T := by
  refine le_trans ?_ H.T_ge_main
  have hι : 1 ≤ ι ^ 2 := by nlinarith [H.ι_ge_one]
  have hP32 := H.P_ge_32
  have hh := H.h_ge
  have hc := H.c₂_ge
  have hε := H.hε
  have hε1 := H.hε1
  rw [le_div_iff₀ (by positivity)]
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hh4 : h ≤ h ^ 4 := by
    have : h ^ 4 = h * h ^ 3 := by ring
    rw [this]; have : 1 ≤ h ^ 3 := one_le_pow₀ (by linarith); nlinarith
  have hP3 : P ≤ P ^ 3 := by
    have : P ^ 3 = P * P ^ 2 := by ring
    rw [this]; have : 1 ≤ P ^ 2 := one_le_pow₀ (by linarith); nlinarith
  have hpos : 0 ≤ 4096 * h * P := by positivity
  calc 4096 * h * P * ε ^ 2 ≤ 4096 * h * P := by nlinarith
    _ ≤ asyncC₂ c₁ * h * P := by nlinarith
    _ ≤ asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P ^ 3 := by
        have h1 : asyncC₂ c₁ * h * P ≤ asyncC₂ c₁ * ι ^ 2 * h * P := by
          have : 0 ≤ asyncC₂ c₁ * h * P := by positivity
          nlinarith
        have h2 : asyncC₂ c₁ * ι ^ 2 * h * P ≤ asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P := by
          have : 0 ≤ asyncC₂ c₁ * ι ^ 2 * P := by positivity
          nlinarith
        have h3 : asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P ≤ asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P ^ 3 := by
          have : 0 ≤ asyncC₂ c₁ * ι ^ 2 * h ^ 4 := by positivity
          nlinarith
        linarith

/-- `2 log(8h²/ε) ≤ log T`, hence also `2 log(4h/ε) ≤ log T`. -/
theorem log_8h2 : 2 * Real.log (8 * h ^ 2 / ε) ≤ P := by
  have hh := H.h_ge
  have hε := H.hε
  have hpos : 0 < 8 * h ^ 2 / ε := by positivity
  rw [← Real.log_rpow hpos, H.hP]
  apply Real.log_le_log (by positivity)
  have : (8 * h ^ 2 / ε) ^ (2 : ℝ) = 64 * h ^ 4 / ε ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  rw [this]
  refine le_trans ?_ H.T_ge_h4
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : 0 ≤ h ^ 4 := by positivity
  linarith

theorem log_4h_le : Real.log (4 * h / ε) ≤ Real.log (8 * h ^ 2 / ε) := by
  have hh := H.h_ge
  have hε := H.hε
  apply Real.log_le_log (by positivity)
  apply div_le_div_of_nonneg_right _ hε.le
  nlinarith

theorem log_4h_pos : 0 < Real.log (4 * h / ε) := by
  have hh := H.h_ge
  have hε := H.hε
  apply Real.log_pos
  rw [lt_div_iff₀ hε]; nlinarith [H.hε1]

/-! ### Rate, epochs, blocks -/

theorem eta_pos : 0 < c₁ * P ^ 3 * h / (T * μm) := by
  have := H.P_pos; have := H.h_ge; have := H.T_pos; have := H.hμ; have := H.hc₁; positivity

theorem eta_le : c₁ * P ^ 3 * h / (T * μm) ≤ c₁ * ε ^ 2 / (asyncC₂ c₁ * ι ^ 2 * h ^ 3) := by
  have hP := H.P_pos; have hh := H.h_ge; have hT := H.T_pos; have hμ := H.hμ
  have hc₁ := H.hc₁; have hc := H.c₂_ge; have hι := H.ι_pos; have hε := H.hε
  have hX : 0 < asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P ^ 3 / ε ^ 2 := by
    have : 0 < asyncC₂ c₁ := by linarith
    positivity
  calc c₁ * P ^ 3 * h / (T * μm) ≤ c₁ * P ^ 3 * h / (asyncC₂ c₁ * ι ^ 2 * h ^ 4 * P ^ 3 / ε ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hX H.hA2
    _ = c₁ * ε ^ 2 / (asyncC₂ c₁ * ι ^ 2 * h ^ 3) := by
        have : asyncC₂ c₁ ≠ 0 := by linarith
        field_simp

theorem eta_le_one : c₁ * P ^ 3 * h / (T * μm) ≤ 1 := by
  refine H.eta_le.trans ?_
  have hh := H.h_ge; have hc := H.c₂_ge; have hι := H.ι_ge_one; have hε := H.hε
  rw [div_le_one (by have : 0 < asyncC₂ c₁ := by linarith
                     positivity)]
  have h1 : c₁ * ε ^ 2 ≤ 1 := by
    have : ε ^ 2 ≤ 1 := by nlinarith [H.hε1]
    nlinarith [H.hc₁1, H.hc₁]
  have h2 : 1 ≤ ι ^ 2 := by nlinarith
  have h3 : 1 ≤ h ^ 3 := one_le_pow₀ (by linarith)
  have : (1 : ℝ) ≤ asyncC₂ c₁ * ι ^ 2 * h ^ 3 := by
    have := mul_le_mul h2 h3 zero_le_one (by positivity)
    nlinarith
  linarith

/-- Number of epochs `K_ep = ⌈2h log(4h/ε)⌉`. -/
theorem Kep_facts : 1 ≤ ⌈2 * h * Real.log (4 * h / ε)⌉₊ ∧
    2 * h * Real.log (4 * h / ε) ≤ (⌈2 * h * Real.log (4 * h / ε)⌉₊ : ℝ) ∧
    (⌈2 * h * Real.log (4 * h / ε)⌉₊ : ℝ) ≤ 2 * h * P ∧
    2 * (⌈2 * h * Real.log (4 * h / ε)⌉₊ : ℝ) ≤ T := by
  have hh := H.h_ge
  have hl := H.log_4h_pos
  have hpos : 0 < 2 * h * Real.log (4 * h / ε) := by positivity
  have hle := Nat.le_ceil (2 * h * Real.log (4 * h / ε))
  have hlt := Nat.ceil_lt_add_one hpos.le
  have hl2 := H.log_4h_le.trans (by linarith [H.log_8h2] : Real.log (8 * h ^ 2 / ε) ≤ P / 2)
  have hP := H.P_ge_32
  have hK : (⌈2 * h * Real.log (4 * h / ε)⌉₊ : ℝ) ≤ 2 * h * P := by nlinarith
  refine ⟨?_, hle, hK, ?_⟩
  · exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      intro h0; rw [h0] at hle; simp at hle; linarith))
  · have := H.T_ge_hP; nlinarith

omit H in
theorem natDiv_ge (a b : ℕ) (hb : 0 < b) (h : 2 * b ≤ a) :
    (a : ℝ) / (2 * b) ≤ ((a / b : ℕ) : ℝ) := by
  have hq : a < (a / b + 1) * b := by
    have := Nat.div_add_mod a b
    have := Nat.mod_lt a hb
    nlinarith
  have hq' : (a : ℝ) < ((a / b : ℕ) + 1) * b := by exact_mod_cast hq
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h' : 2 * (b : ℝ) ≤ a := by exact_mod_cast h
  rw [div_le_iff₀ (by positivity)]
  nlinarith

omit H in

omit H in
theorem natDiv_mul_ge (a b : ℕ) (hb : 0 < b) : (a : ℝ) - b < ((a / b : ℕ) : ℝ) * b := by
  have hq : a < (a / b + 1) * b := by
    have := Nat.div_add_mod a b
    have := Nat.mod_lt a hb
    nlinarith
  have hq' : (a : ℝ) < ((a / b : ℕ) + 1) * b := by exact_mod_cast hq
  linarith

/-- Window length `ℓ = ⌊T/K_ep⌋ ≥ T/(4hP)`. -/
theorem ell_ge {Tn K : ℕ} (hTn : T = Tn) (hK1 : 1 ≤ K) (hK : (K : ℝ) ≤ 2 * h * P)
    (hK2 : 2 * (K : ℝ) ≤ T) : T / (4 * h * P) ≤ ((Tn / K : ℕ) : ℝ) := by
  have hh := H.h_ge; have hP := H.P_pos
  have h2 : 2 * K ≤ Tn := by rw [hTn] at hK2; exact_mod_cast hK2
  refine le_trans ?_ (natDiv_ge Tn K (by omega) h2)
  rw [← hTn]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  apply div_le_div_of_nonneg_left (by linarith [H.T_pos]) (by positivity)
  linarith

/-- Block length `b = ⌈8 t̄/μ_min⌉`. -/
theorem block_facts : 1 ≤ ⌈8 * tb / μm⌉₊ ∧ 8 * tb ≤ (⌈8 * tb / μm⌉₊ : ℝ) * μm ∧
    (⌈8 * tb / μm⌉₊ : ℝ) ≤ 9 * tb / μm := by
  have hμ := H.hμ; have htb := H.htb
  have hpos : 0 < 8 * tb / μm := by positivity
  have hle := Nat.le_ceil (8 * tb / μm)
  have hlt := Nat.ceil_lt_add_one hpos.le
  have h1 : 1 ≤ tb / μm := by rw [le_div_iff₀ hμ]; linarith [H.hμ1]
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      intro h0; rw [h0] at hle; simp at hle; linarith))
  · rw [div_le_iff₀ hμ] at hle; linarith
  · have : 8 * tb / μm + 1 ≤ 9 * tb / μm := by
      have e : 9 * tb / μm = 8 * tb / μm + tb / μm := by ring
      linarith
    linarith

/-- `ℓ ≥ 2b` and `J = ⌊ℓ/b⌋ ≥ 50 ι`. -/
theorem J_facts {ℓ b : ℕ} (hℓ : T / (4 * h * P) ≤ (ℓ : ℝ)) (hb1 : 1 ≤ b)
    (hb : (b : ℝ) ≤ 9 * tb / μm) :
    2 * b ≤ ℓ ∧ 50 * ι ≤ ((ℓ / b : ℕ) : ℝ) ∧ (ℓ : ℝ) / 2 ≤ ((ℓ / b : ℕ) : ℝ) * b := by
  have hh := H.h_ge; have hP := H.P_ge_32; have hμ := H.hμ; have htb := H.htb
  have hι := H.ι_ge_P; have hc := H.c₂_ge
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb1
  have hP0 : (0 : ℝ) < 4 * P := by linarith
  have hhP0 : (0 : ℝ) < 4 * h * P := by positivity
  -- ℓ ≥ T μ /(4hP μ) ≥ c₂ ι² t̄ /(4 P μ)
  have hA3 := H.hA3
  have hℓμ : asyncC₂ c₁ * ι ^ 2 * tb / (4 * P) ≤ (ℓ : ℝ) * μm := by
    have : T * μm / (4 * h * P) ≤ (ℓ : ℝ) * μm := by
      rw [mul_div_right_comm]; exact mul_le_mul_of_nonneg_right hℓ hμ.le
    refine le_trans ?_ this
    rw [div_le_div_iff₀ hP0 hhP0]
    have : asyncC₂ c₁ * ι ^ 2 * tb * (4 * h * P) = (asyncC₂ c₁ * ι ^ 2 * h * tb) * (4 * P) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hA3 (by positivity)
  have hι2 : 1024 * ι * tb ≤ asyncC₂ c₁ * ι ^ 2 * tb / (4 * P) := by
    rw [le_div_iff₀ hP0]
    have : 0 ≤ ι * tb := by nlinarith
    have h1 : 4096 * (ι * tb) * P ≤ asyncC₂ c₁ * (ι * tb) * P := by
      have := mul_le_mul_of_nonneg_right hc this
      nlinarith
    have h2 : asyncC₂ c₁ * (ι * tb) * P ≤ asyncC₂ c₁ * (ι * tb) * ι := by
      have : 0 ≤ asyncC₂ c₁ * (ι * tb) := mul_nonneg (by linarith) this
      exact mul_le_mul_of_nonneg_left hι this
    nlinarith
  have hℓb : 18 * tb ≤ (ℓ : ℝ) * μm := by nlinarith
  have h2b : 2 * (b : ℝ) ≤ ℓ := by
    have : 2 * (b : ℝ) * μm ≤ 18 * tb := by
      rw [le_div_iff₀ hμ] at hb; linarith
    nlinarith
  have h2b' : 2 * b ≤ ℓ := by exact_mod_cast h2b
  have hJ := natDiv_ge ℓ b (by omega) h2b'
  have hJb := natDiv_mul_ge ℓ b (by omega)
  refine ⟨h2b', ?_, by linarith⟩
  refine le_trans ?_ hJ
  rw [le_div_iff₀ (by positivity)]
  have : (b : ℝ) * μm ≤ 9 * tb := by rw [le_div_iff₀ hμ] at hb; linarith
  have hι0 : 0 ≤ ι := by linarith
  nlinarith

/-! ### Confidence levels, radius, contraction and final error -/

theorem T_ge_32 : 32 ≤ T := by
  have := H.T_ge_hP; have := H.h_ge; have := H.P_ge_32; nlinarith

theorem delta1_facts : 0 < δ / (4 * SA * T * (T + 1) ^ 2) ∧ δ / (4 * SA * T * (T + 1) ^ 2) < 1 ∧
    0 < Real.log (2 / (δ / (4 * SA * T * (T + 1) ^ 2))) ∧
    Real.log (2 / (δ / (4 * SA * T * (T + 1) ^ 2))) ≤ 4 * ι := by
  have hδ := H.hδ; have hδ1 := H.hδ1; have hSA := H.hSA; have hT := H.T_ge_32
  have hD : 1 ≤ 4 * SA * T * (T + 1) ^ 2 := by
    have : 1 ≤ SA * T := by nlinarith
    have : 1 ≤ (T + 1) ^ 2 := by nlinarith
    nlinarith
  have hpos : 0 < δ / (4 * SA * T * (T + 1) ^ 2) := by positivity
  have hlt : δ / (4 * SA * T * (T + 1) ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have he : 2 / (δ / (4 * SA * T * (T + 1) ^ 2)) = 8 * (SA * T / δ) * (T + 1) ^ 2 := by
    field_simp; ring
  set X := SA * T / δ with hX
  have hXT : T ≤ X := by rw [hX, le_div_iff₀ hδ]; nlinarith
  refine ⟨hpos, hlt, Real.log_pos (by rw [lt_div_iff₀ hpos]; linarith), ?_⟩
  rw [he, H.hι, ← hX, show 4 * Real.log X = Real.log (X ^ 4) by
    rw [Real.log_pow]; norm_num]
  apply Real.log_le_log (by positivity)
  have h1 : (T + 1) ^ 2 ≤ 4 * T ^ 2 := by nlinarith
  have hX0 : 0 ≤ X := by linarith
  calc 8 * X * (T + 1) ^ 2 ≤ 8 * X * (4 * T ^ 2) := by gcongr
    _ = X * (32 * T ^ 2) := by ring
    _ ≤ X * T ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ hX0
        nlinarith
    _ ≤ X * X ^ 3 := by gcongr
    _ = X ^ 4 := by ring

theorem rho_le {Lr : ℝ} (hL0 : 0 ≤ Lr) (hL : Lr ≤ 4 * ι) :
    8 * (c₁ * P ^ 3 * h / (T * μm)) * Lr ≤ ε ^ 2 / (128 * h ^ 3) := by
  have hη := H.eta_le
  have hη0 := H.eta_pos
  have hh := H.h_ge; have hc := H.c₂_ge; have hι := H.ι_ge_one; have hε := H.hε
  have hc₁ := H.hc₁; have hc₁1 := H.hc₁1
  have hc0 : 0 < asyncC₂ c₁ := by linarith
  calc 8 * (c₁ * P ^ 3 * h / (T * μm)) * Lr
      ≤ 8 * (c₁ * ε ^ 2 / (asyncC₂ c₁ * ι ^ 2 * h ^ 3)) * (4 * ι) := by gcongr
    _ = 32 * c₁ * ε ^ 2 / (asyncC₂ c₁ * ι * h ^ 3) := by field_simp; ring
    _ ≤ 32 * 1 * ε ^ 2 / (4096 * 1 * h ^ 3) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by positivity)
        gcongr
    _ = ε ^ 2 / (128 * h ^ 3) := by ring

theorem theta_le {ℓ : ℝ} (hℓ : T / (4 * h * P) ≤ ℓ) :
    Real.exp (-(c₁ * P ^ 3 * h / (T * μm) * (ℓ * μm / 8))) ≤ ε / (8 * h ^ 2) := by
  have hh := H.h_ge; have hP := H.P_ge_32; have hT := H.T_pos; have hμ := H.hμ
  have hc₁ := H.hc₁; have hε := H.hε
  have hcP := H.P_ge
  have hcP' : 32 ≤ c₁ * P := by rw [div_le_iff₀ hc₁] at hcP; linarith
  have hm : c₁ * P ^ 2 / 32 ≤ c₁ * P ^ 3 * h / (T * μm) * (ℓ * μm / 8) := by
    have e : c₁ * P ^ 3 * h / (T * μm) * (ℓ * μm / 8) = c₁ * P ^ 3 * h / (8 * T) * ℓ := by
      field_simp
    rw [e]
    calc c₁ * P ^ 2 / 32 = c₁ * P ^ 3 * h / (8 * T) * (T / (4 * h * P)) := by
          field_simp; ring
      _ ≤ c₁ * P ^ 3 * h / (8 * T) * ℓ := by
          apply mul_le_mul_of_nonneg_left hℓ; positivity
  have hlog := H.log_8h2
  have hlog0 : 0 ≤ Real.log (8 * h ^ 2 / ε) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hε]; nlinarith [H.hε1]
  have hge : Real.log (8 * h ^ 2 / ε) ≤ c₁ * P ^ 3 * h / (T * μm) * (ℓ * μm / 8) := by
    have : P ≤ c₁ * P ^ 2 / 32 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith
  calc Real.exp (-(c₁ * P ^ 3 * h / (T * μm) * (ℓ * μm / 8)))
      ≤ Real.exp (-Real.log (8 * h ^ 2 / ε)) := Real.exp_le_exp.mpr (by linarith)
    _ = ε / (8 * h ^ 2) := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp

theorem fail_F {K : ℝ} (hK : K ≤ T) (hK0 : 0 ≤ K) :
    2 * SA * K * (T + 1) * (T + 1) * (δ / (4 * SA * T * (T + 1) ^ 2)) ≤ δ / 2 := by
  have hδ := H.hδ; have hSA := H.hSA; have hT := H.T_pos
  have e : 2 * SA * K * (T + 1) * (T + 1) * (δ / (4 * SA * T * (T + 1) ^ 2)) = K * δ / (2 * T) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem fail_V {K J : ℝ} (hK : K ≤ T) (hK0 : 0 ≤ K) (hJ : 50 * ι ≤ J) :
    SA * K * Real.exp (-(J / 25)) ≤ δ / 2 := by
  have hδ := H.hδ; have hδ1 := H.hδ1; have hSA := H.hSA; have hT := H.T_ge_32
  have h1 : Real.exp (-(J / 25)) ≤ (δ / (SA * T)) ^ 2 := by
    have : Real.exp (-(J / 25)) ≤ Real.exp (-(2 * ι)) := Real.exp_le_exp.mpr (by linarith)
    refine this.trans (le_of_eq ?_)
    rw [H.hι, show -(2 * Real.log (SA * T / δ)) = Real.log ((SA * T / δ) ^ 2)⁻¹ by
      rw [Real.log_inv, Real.log_pow]; ring, Real.exp_log (by positivity)]
    field_simp
  calc SA * K * Real.exp (-(J / 25)) ≤ SA * K * (δ / (SA * T)) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = K * δ ^ 2 / (SA * T ^ 2) := by field_simp
    _ ≤ δ / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : K * δ ≤ T := by nlinarith
        have : 2 * T ≤ SA * T ^ 2 := by nlinarith
        nlinarith

theorem one_sub_gamma : 1 - γ = 1 / h := by
  have := H.h_mul; have := H.h_ge
  field_simp; linarith

theorem rho_h3 {ρ : ℝ} (hρ : ρ ≤ ε ^ 2 / (128 * h ^ 3)) : ρ * h ^ 3 ≤ ε ^ 2 / 128 := by
  have hh := H.h_ge
  have := mul_le_mul_of_nonneg_right hρ (by positivity : (0 : ℝ) ≤ h ^ 3)
  have e2 : ε ^ 2 / (128 * h ^ 3) * h ^ 3 = ε ^ 2 / 128 := by field_simp
  linarith

theorem sqrt_term_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2 / (128 * h ^ 3)) :
    Real.sqrt (γ * ρ / (2 * (1 - γ) ^ 3)) ≤ ε / 4 := by
  have hh := H.h_ge; have hε := H.hε; have hγ := H.hγ; have hγ1 := H.hγ1
  have e : γ * ρ / (2 * (1 - γ) ^ 3) = γ * (ρ * h ^ 3) / 2 := by
    rw [H.one_sub_gamma]; field_simp
  rw [e]
  have h1 := H.rho_h3 hρ
  have h2 : γ * (ρ * h ^ 3) ≤ ρ * h ^ 3 := by
    have : 0 ≤ ρ * h ^ 3 := by positivity
    nlinarith
  have h3 : γ * (ρ * h ^ 3) / 2 ≤ (ε / 4) ^ 2 := by
    have : (ε / 4) ^ 2 = ε ^ 2 / 16 := by ring
    rw [this]
    have : 0 ≤ ε ^ 2 := sq_nonneg ε
    linarith
  calc Real.sqrt (γ * (ρ * h ^ 3) / 2) ≤ Real.sqrt ((ε / 4) ^ 2) := Real.sqrt_le_sqrt h3
    _ = ε / 4 := Real.sqrt_sq (by positivity)

theorem shift_term_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2 / (128 * h ^ 3)) :
    2 * ρ / (1 - γ) ^ 2 ≤ ε / 4 := by
  have hh := H.h_ge; have hε := H.hε; have hε1 := H.hε1
  have e : 2 * ρ / (1 - γ) ^ 2 = 2 * (ρ * h ^ 2) := by rw [H.one_sub_gamma]; field_simp
  rw [e]
  have h1 := H.rho_h3 hρ
  have h2 : 2 * (ρ * h ^ 2) ≤ ρ * h ^ 3 := by
    have : 0 ≤ ρ * h ^ 2 := by positivity
    have e3 : ρ * h ^ 3 = (ρ * h ^ 2) * h := by ring
    rw [e3]; nlinarith
  have h3 : ε ^ 2 ≤ ε := by nlinarith
  linarith

theorem contraction_lt {θ : ℝ} (hθ : θ ≤ ε / (8 * h ^ 2)) :
    γ + θ ≤ 1 - 1 / (2 * h) := by
  have hh := H.h_ge; have hε := H.hε; have hε1 := H.hε1
  have hu : 0 < 1 / (2 * h) := by positivity
  have hθ' : θ ≤ 1 / (2 * h) / 4 := by
    refine hθ.trans ?_
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hg : γ = 1 - 2 * (1 / (2 * h)) := by
    have := H.one_sub_gamma
    have e : 1 / h = 2 * (1 / (2 * h)) := by field_simp
    linarith
  linarith

theorem pow_term_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ ε / (8 * h ^ 2)) {K : ℕ}
    (hK : 2 * h * Real.log (4 * h / ε) ≤ K) : (γ + θ) ^ K * h ≤ ε / 4 := by
  have hh := H.h_ge; have hε := H.hε; have hγ := H.hγ
  have ha := H.contraction_lt hθ
  have h1 : γ + θ ≤ Real.exp (-(1 / (2 * h))) := by
    have := Real.add_one_le_exp (-(1 / (2 * h))); linarith
  have h2 : (γ + θ) ^ K ≤ Real.exp (-(1 / (2 * h))) ^ K :=
    pow_le_pow_left₀ (by linarith) h1 K
  have h3 : Real.log (4 * h / ε) ≤ K * (1 / (2 * h)) := by
    rw [show (K : ℝ) * (1 / (2 * h)) = K / (2 * h) by ring, le_div_iff₀ (by positivity)]
    linarith
  have h4 : Real.exp (-(1 / (2 * h))) ^ K ≤ ε / (4 * h) := by
    rw [← Real.exp_nat_mul]
    calc Real.exp (K * -(1 / (2 * h))) ≤ Real.exp (-Real.log (4 * h / ε)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = ε / (4 * h) := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  calc (γ + θ) ^ K * h ≤ ε / (4 * h) * h := by
        apply mul_le_mul_of_nonneg_right (h2.trans h4); linarith
    _ = ε / 4 := by field_simp

theorem tail_term_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ ε / (8 * h ^ 2)) :
    θ * h / (1 - (γ + θ)) ≤ ε / 4 := by
  have hh := H.h_ge; have hε := H.hε
  have ha := H.contraction_lt hθ
  have hu : 0 < 1 / (2 * h) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have h1 : θ * h ≤ ε / (8 * h ^ 2) * h := mul_le_mul_of_nonneg_right hθ (by linarith)
  have e : ε / (8 * h ^ 2) * h = ε / 4 * (1 / (2 * h)) := by field_simp; ring
  have h2 : ε / 4 * (1 / (2 * h)) ≤ ε / 4 * (1 - (γ + θ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- The final accuracy budget. -/
theorem final_le {ρ θ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2 / (128 * h ^ 3)) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ ε / (8 * h ^ 2)) {K : ℕ} (hK : 2 * h * Real.log (4 * h / ε) ≤ K) :
    γ + θ < 1 ∧
    (γ + θ) ^ K * h + θ * h / (1 - (γ + θ)) +
      (Real.sqrt (γ * ρ / (2 * (1 - γ) ^ 3)) + 2 * ρ / (1 - γ) ^ 2) ≤ ε := by
  have hh := H.h_ge
  have hu : 0 < 1 / (2 * h) := by positivity
  have ha := H.contraction_lt hθ
  refine ⟨by linarith, ?_⟩
  have := H.pow_term_le hθ0 hθ hK
  have := H.tail_term_le hθ0 hθ
  have := H.sqrt_term_le hρ0 hρ
  have := H.shift_term_le hρ0 hρ
  linarith

end ArithHyp

end StatisticalRL.AsyncQ

import Formalization.ModelFree.QLearningLowerBoundVaryingOverestimation
import Formalization.ModelFree.QLearningLowerBoundVaryingState2

/-!
# Theorem 4.7 (`thm:LB-example-Q-generative`), case (i): rescaled linear learning rates

`chapters/generative_model_model_free.tex:969–982`. The source proves only case (ii) and defers
case (i) to li2024q (line 2711; `docs/SOURCE-ISSUES.md#C30`); this proof is new.

For every `γ ∈ [3/4,1)`, `T ≥ 16/(1-γ)²` and `c_η > 0`, synchronous Q-learning from `Q₀ = 0` with
`η_t = 1/(1 + c_η(1-γ)t)` on `qLbMDP γ` (4 states, 2 actions) satisfies
`max_s E[(V_T(s) - V⋆(s))²] ≥ 10⁻⁹/((1-γ)⁴ T log² T)`. With `ε = 1-γ`, `κ = 1-γp = 4ε/3`,
`D = c_η ε`, `Σ = ∑_{t=1}^T κ η_t`, `L = log T`:
* (A) `D > 1`: `Σ ≤ κ(1+L)/D`, the squared bias of state 2 is `≥ (3/(4ε))² e^{-4(1+L)/c_η}`, enough
  because either `(1+L)/c_η ≤ 1` or `ε > 1/(1+L)` and `e^{-4(1+L)/c_η} ≥ 1/(eT)`;
* (B) `D ≤ 1`, `Σ ≤ 1/2`: the squared bias of state 2 is `≥ (3/(4ε))² e^{-3/2}`;
* (C) `D ≤ 1`, `Σ > 1/2`: then `c_η < 8L`, `Π_κ(1,T) ≤ 6/7`, the time-varying Lemma 4.15 gives
  `E ξ_{t,max} ≥ (5/1536) min(√(η_T/ε), 1)` for `1 ≤ t ≤ T`, and the over-estimation recursion
  together with state 3 gives the bound.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

/-! ### Scalar parts -/

theorem qLbv_exp_neg_four_ge : 1 / 100 ≤ Real.exp (-4) := by
  have he : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  have : Real.exp 4 ≤ 100 := by
    rw [h4]
    calc Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
      _ ≤ 100 := by norm_num
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (by norm_num) (Real.exp_pos 4)]
  linarith

theorem qLbv_exp_neg_one_ge : 1 / 3 ≤ Real.exp (-1) := by
  have he : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (by norm_num) (Real.exp_pos 1)]
  linarith

/-- From a lower bound `P ≥ e^{-y}` on `Π_κ(0,T)`, the squared bias `(P·V⋆)²` of state 2 beats the
target as soon as `16·10⁻⁹ ≤ 9 e^{-2y} ε² T L²`. -/
theorem qLbv_bias_scalar (ε T L y P : ℝ) (hε0 : 0 < ε) (hT0 : 0 < T) (hL0 : 0 < L)
    (hP : Real.exp (-y) ≤ P)
    (hK : 16 / 10 ^ 9 ≤ 9 * Real.exp (-(2 * y)) * (ε ^ 2 * T * L ^ 2)) :
    1 / 10 ^ 9 / (ε ^ 4 * T * L ^ 2) ≤ (P * (3 / (4 * ε))) ^ 2 := by
  have hP2 : Real.exp (-(2 * y)) ≤ P ^ 2 := by
    have e : Real.exp (-(2 * y)) = Real.exp (-y) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [e]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hP 2
  rw [div_le_iff₀ (by positivity)]
  have e : (P * (3 / (4 * ε))) ^ 2 * (ε ^ 4 * T * L ^ 2) = P ^ 2 * (9 * (ε ^ 2 * T * L ^ 2)) / 16 := by
    field_simp; ring
  rw [e]
  have := mul_le_mul_of_nonneg_right hP2 (by positivity : (0 : ℝ) ≤ 9 * (ε ^ 2 * T * L ^ 2))
  have e2 : Real.exp (-(2 * y)) * (9 * (ε ^ 2 * T * L ^ 2)) =
      9 * Real.exp (-(2 * y)) * (ε ^ 2 * T * L ^ 2) := by ring
  linarith

/-- Case A arithmetic: `16·10⁻⁹ ≤ 9 e^{-4(1+L)/c} ε² T L²` when `cε > 1`, uniformly in `c`. -/
theorem qLbv_caseA_K (ε T L c : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 4) (hT0 : 0 < T)
    (hRT : 16 ≤ ε ^ 2 * T) (hL1 : 1 ≤ L) (hLT : Real.exp L = T) (hD : 1 < c * ε) :
    16 / 10 ^ 9 ≤ 9 * Real.exp (-(2 * (2 * (1 + L) / c))) * (ε ^ 2 * T * L ^ 2) := by
  have hc0 : 0 < c := by
    by_contra h; push_neg at h; nlinarith
  have hc4 : 4 < c := by
    by_contra h; push_neg at h; nlinarith
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  rcases le_or_gt ((1 + L) / c) 1 with hu | hu
  · have h1 : -4 ≤ -(2 * (2 * (1 + L) / c)) := by
      have : 2 * (2 * (1 + L) / c) = 4 * ((1 + L) / c) := by ring
      rw [this]; linarith
    have h2 : 1 / 100 ≤ Real.exp (-(2 * (2 * (1 + L) / c))) :=
      qLbv_exp_neg_four_ge.trans (Real.exp_le_exp.mpr h1)
    have h3 : 16 ≤ ε ^ 2 * T * L ^ 2 := by nlinarith
    nlinarith
  · have hcL : c < 1 + L := by rwa [one_lt_div hc0] at hu
    have hεL : 1 / 4 < ε ^ 2 * L ^ 2 := by
      have h1 : 1 < ε * (1 + L) := by nlinarith
      have h2 : 1 < 2 * (ε * L) := by nlinarith
      nlinarith
    have h1 : -(1 + L) ≤ -(2 * (2 * (1 + L) / c)) := by
      have : 2 * (2 * (1 + L) / c) ≤ 1 + L := by
        rw [show 2 * (2 * (1 + L) / c) = 4 * (1 + L) / c by ring, div_le_iff₀ hc0]
        nlinarith
      linarith
    have h2 : Real.exp (-1) / T ≤ Real.exp (-(2 * (2 * (1 + L) / c))) := by
      have e : Real.exp (-(1 + L)) = Real.exp (-1) / T := by
        rw [neg_add, Real.exp_add, Real.exp_neg L, hLT, div_eq_mul_inv]
      rw [← e]; exact Real.exp_le_exp.mpr h1
    have h3 : 1 / (3 * T) ≤ Real.exp (-(2 * (2 * (1 + L) / c))) := by
      have : 1 / (3 * T) ≤ Real.exp (-1) / T := by
        rw [show 1 / (3 * T) = (1 / 3) / T by field_simp]
        exact div_le_div_of_nonneg_right qLbv_exp_neg_one_ge hT0.le
      linarith
    have h4 : 9 * (1 / (3 * T)) * (ε ^ 2 * T * L ^ 2) ≤
        9 * Real.exp (-(2 * (2 * (1 + L) / c))) * (ε ^ 2 * T * L ^ 2) := by
      have : 0 ≤ ε ^ 2 * T * L ^ 2 := by positivity
      nlinarith
    have e : 9 * (1 / (3 * T)) * (ε ^ 2 * T * L ^ 2) = 3 * (ε ^ 2 * L ^ 2) := by
      field_simp; ring
    linarith

/-- Case C arithmetic: from `c < 8L` and `b ≥ (5/1536) min(√(η_T/ε), 1)`, `η_T = 1/(1 + cεT)`,
`(b/(28ε))² ≥ 10⁻⁹/(ε⁴ T L²)`. Uses `1 ≤ εTL` (from `εT ≥ 16/ε ≥ 64` and `L ≥ 1`). -/
theorem qLbv_caseC_final (ε T L c b : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 4) (hRT : 16 ≤ ε ^ 2 * T)
    (hL1 : 1 ≤ L) (hc0 : 0 < c) (hc : c < 8 * L)
    (hb : 5 / 1536 * min (Real.sqrt ((1 / (1 + c * ε * T)) / ε)) 1 ≤ b) :
    1 / 10 ^ 9 / (ε ^ 4 * T * L ^ 2) ≤ (b / (28 * ε)) ^ 2 := by
  have hT0 : 0 < T := by
    by_contra h; push_neg at h; nlinarith [sq_nonneg ε]
  have hεT : 64 ≤ ε * T := by
    by_contra h; push_neg at h
    have : ε * (ε * T) < ε * 64 := mul_lt_mul_of_pos_left h hε0
    nlinarith
  -- fix (5) of the plan check: `1 ≤ εTL`, proved explicitly
  have hεTL : 1 ≤ ε * T * L := by nlinarith
  have hden : 1 + c * ε * T ≤ 9 * (ε * T * L) := by
    have : c * (ε * T) ≤ 8 * L * (ε * T) := mul_le_mul_of_nonneg_right hc.le (by positivity)
    nlinarith
  set y := 1 / (9 * ε ^ 2 * T * L) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_one (by positivity)]
    nlinarith
  have hxy : y ≤ (1 / (1 + c * ε * T)) / ε := by
    rw [hy, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hs : Real.sqrt y ≤ min (Real.sqrt ((1 / (1 + c * ε * T)) / ε)) 1 :=
    le_min (Real.sqrt_le_sqrt hxy) (Real.sqrt_le_one.mpr hy1)
  have hb0 : 5 / 1536 * Real.sqrt y ≤ b := by
    have := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 5 / 1536)
    linarith
  have hb2 : 25 / 2359296 * y ≤ b ^ 2 := by
    have h0 : 0 ≤ 5 / 1536 * Real.sqrt y := by positivity
    have := pow_le_pow_left₀ h0 hb0 2
    rw [mul_pow, Real.sq_sqrt hy0.le] at this
    linarith
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have e : y * (ε ^ 4 * T * L ^ 2) = ε ^ 2 * L / 9 := by
    rw [hy]; field_simp
  have h1 : 25 / 2359296 * y * (ε ^ 4 * T * L ^ 2) ≤ b ^ 2 * (ε ^ 4 * T * L ^ 2) :=
    mul_le_mul_of_nonneg_right hb2 (by positivity)
  have h2 : 1 / 10 ^ 9 * (28 * ε) ^ 2 ≤ 25 / 2359296 * (ε ^ 2 * L / 9) := by
    have : 0 ≤ ε ^ 2 := sq_nonneg ε
    nlinarith
  have e2 : 25 / 2359296 * y * (ε ^ 4 * T * L ^ 2) = 25 / 2359296 * (y * (ε ^ 4 * T * L ^ 2)) := by
    ring
  rw [e2, e] at h1
  linarith

/-! ### Assembly -/

/-- State 2: `(Π_{1-γp}(0,T) · V⋆(2))² ≤ E[(V_T(2) - V⋆(2))²]` for any schedule in `[0,1]`. -/
theorem qLbv_state2_bias (γ : ℝ) (hγ' : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) (η : ℕ → ℝ)
    (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1) (T : ℕ) :
    (qLbvProd η (1 - γ * qHardP γ) 0 T * (3 / (4 * (1 - γ)))) ^ 2 ≤
      ∫ d, (qLearningValue (qLbMDP γ hγ' hγ1)
        (qSampledIterate (qLbMDP γ hγ' hγ1) η T (fun _ _ ↦ 0) d) 2 -
        (qLbMDP γ hγ' hγ1).trajectoryExpectedValue (qLbMDP γ hγ' hγ1).optimalGreedyPolicy 2) ^ 2
          ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T := by
  have hVs : ∀ s, (qLbMDP γ hγ' hγ1).trajectoryExpectedValue
      (qLbMDP γ hγ' hγ1).optimalGreedyPolicy s = qHardValue γ s :=
    fun s ↦ congrFun (qLbMDP_value γ hγ' hγ1) s
  have hout := qLbv_output_ae γ η hγ' hγ1 hη T
  have hE2 : ∫ d, (qLearningValue (qLbMDP γ hγ' hγ1)
      (qSampledIterate (qLbMDP γ hγ' hγ1) η T (fun _ _ ↦ 0) d) 2 -
      (qLbMDP γ hγ' hγ1).trajectoryExpectedValue (qLbMDP γ hγ' hγ1).optimalGreedyPolicy 2) ^ 2
        ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T =
      ∫ d, (qLbvChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T - 1 / (1 - γ * qHardP γ)) ^ 2
        ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T := by
    apply integral_congr_ae
    filter_upwards [hout] with d hd
    rw [hd.1, hVs 2]
    simp [qHardValue]
  rw [hE2]
  have hmean := qLbv_state2_mean γ hγ' hγ1 T η T le_rfl
  have hsq := qLb_sq_integral_le (qLbMDP γ hγ' hγ1) T
    (fun d ↦ qLbvChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T) (1 / (1 - γ * qHardP γ))
  have e : (∫ d, qLbvChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T
      ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T - 1 / (1 - γ * qHardP γ)) ^ 2 =
      (qLbvProd η (1 - γ * qHardP γ) 0 T * (3 / (4 * (1 - γ)))) ^ 2 := by
    rw [show (∫ d, qLbvChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T
      ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T - 1 / (1 - γ * qHardP γ)) ^ 2 =
      (1 / (1 - γ * qHardP γ) - ∫ d, qLbvChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T
      ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T) ^ 2 by ring, hmean, qLb_vstar_eq γ hγ' hγ1]
  rw [e] at hsq
  exact hsq

/-- Common consequences of the hypotheses of case (i). -/
theorem qLbv_setup (γ : ℝ) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (T : ℕ) (hT : 16 / (1 - γ) ^ 2 ≤ T) :
    16 ≤ (1 - γ) ^ 2 * T ∧ (0 : ℝ) < T ∧ 1 ≤ Real.log T ∧ 1 ≤ T ∧
      Real.exp (Real.log T) = T := by
  obtain ⟨hRT, hTpos, hlog, -, -⟩ := qLb_T_facts γ T hγ hγ1 hT
  have hT1 : 1 ≤ T := by
    by_contra h; push_neg at h
    have : T = 0 := by omega
    rw [this] at hTpos; simp at hTpos
  exact ⟨hRT, hTpos, hlog, hT1, Real.exp_log hTpos⟩

/-- Cases A and B: the squared bias of state 2 beats the target when `c_η(1-γ) > 1`, or when
`c_η(1-γ) ≤ 1` and `∑_{t ≤ T} (1-γp) η_t ≤ 1/2`. -/
theorem qLbv_caseAB (γ : ℝ) (hγ : 3 / 4 ≤ γ) (hγ' : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) (T : ℕ)
    (hT : 16 / (1 - γ) ^ 2 ≤ T) (cη : ℝ) (hcη : 0 < cη)
    (hAB : 1 < cη * (1 - γ) ∨ ∑ j ∈ Finset.Ioc 0 T,
      (1 - γ * qHardP γ) * (1 / (1 + cη * (1 - γ) * j)) ≤ 1 / 2) :
    1 / 10 ^ 9 / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤
      ∫ d, (qLearningValue (qLbMDP γ hγ' hγ1)
        (qSampledIterate (qLbMDP γ hγ' hγ1) (fun t ↦ 1 / (1 + cη * (1 - γ) * t)) T
          (fun _ _ ↦ 0) d) 2 -
        (qLbMDP γ hγ' hγ1).trajectoryExpectedValue (qLbMDP γ hγ' hγ1).optimalGreedyPolicy 2) ^ 2
          ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T := by
  obtain ⟨hRT, hTpos, hlog, -, hLT⟩ := qLbv_setup γ hγ hγ1 T hT
  have hg : 0 < 1 - γ := by linarith
  have hg4 : 1 - γ ≤ 1 / 4 := by linarith
  have hL0 : 0 < Real.log T := by linarith
  have hD0 : 0 ≤ cη * (1 - γ) := by positivity
  have hη := qLbvRate_bounds (cη * (1 - γ)) hD0
  have hid := qLb_one_sub_gamma_p γ hγ'
  have hκ0 : 0 ≤ 1 - γ * qHardP γ := by rw [hid]; positivity
  have hκ13 : 1 - γ * qHardP γ ≤ 1 / 3 := by rw [hid]; linarith
  have hP0 := qLbvProd_ge_exp (fun t : ℕ ↦ 1 / (1 + cη * (1 - γ) * t)) (1 - γ * qHardP γ) 0 T
    (fun j ↦ mul_nonneg hκ0 (hη j).1)
    (fun j ↦ (mul_le_of_le_one_right hκ0 (hη j).2).trans hκ13)
  refine le_trans ?_ (qLbv_state2_bias γ hγ' hγ1 _ hη T)
  rcases hAB with hA | hB
  · ---------------- Case A
    have hsum := qLbvRate_sum_zero (cη * (1 - γ)) (by positivity) T
    have h1 : ∑ j ∈ Finset.Ioc 0 T, (1 - γ * qHardP γ) * (1 / (1 + cη * (1 - γ) * j)) ≤
        (1 - γ * qHardP γ) * (1 / (cη * (1 - γ)) * (1 + Real.log T)) := by
      rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hsum hκ0
    have e : 3 / 2 * ((1 - γ * qHardP γ) * (1 / (cη * (1 - γ)) * (1 + Real.log T))) =
        2 * (1 + Real.log T) / cη := by
      rw [hid]; field_simp; ring
    have hP : Real.exp (-(2 * (1 + Real.log T) / cη)) ≤
        qLbvProd (fun t : ℕ ↦ 1 / (1 + cη * (1 - γ) * t)) (1 - γ * qHardP γ) 0 T :=
      (Real.exp_le_exp.mpr (by linarith)).trans hP0
    exact qLbv_bias_scalar (1 - γ) T (Real.log T) _ _ hg hTpos hL0 hP
      (qLbv_caseA_K (1 - γ) T (Real.log T) cη hg hg4 hTpos hRT hlog hLT hA)
  · ---------------- Case B
    have hP : Real.exp (-(3 / 4)) ≤
        qLbvProd (fun t : ℕ ↦ 1 / (1 + cη * (1 - γ) * t)) (1 - γ * qHardP γ) 0 T :=
      (Real.exp_le_exp.mpr (by linarith)).trans hP0
    refine qLbv_bias_scalar (1 - γ) T (Real.log T) _ _ hg hTpos hL0 hP ?_
    have h1 : 1 / 100 ≤ Real.exp (-(2 * (3 / 4 : ℝ))) :=
      qLbv_exp_neg_four_ge.trans (Real.exp_le_exp.mpr (by norm_num))
    have h2 : 16 ≤ (1 - γ) ^ 2 * T * Real.log T ^ 2 := by
      have : 1 ≤ Real.log T ^ 2 := by nlinarith
      have h3 : (1 - γ) ^ 2 * T * 1 ≤ (1 - γ) ^ 2 * T * Real.log T ^ 2 :=
        mul_le_mul_of_nonneg_left this (by positivity)
      linarith
    have := mul_le_mul h1 h2 (by norm_num) (Real.exp_pos _).le
    linarith

/-- Case C: `c_η(1-γ) ≤ 1` and `∑_{t ≤ T} (1-γp) η_t > 1/2`; over-estimation at states 1 and 3. -/
theorem qLbv_caseC (γ : ℝ) (hγ : 3 / 4 ≤ γ) (hγ' : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) (T : ℕ)
    (hT : 16 / (1 - γ) ^ 2 ≤ T) (cη : ℝ) (hcη : 0 < cη) (hD1 : cη * (1 - γ) ≤ 1)
    (hC : 1 / 2 < ∑ j ∈ Finset.Ioc 0 T, (1 - γ * qHardP γ) * (1 / (1 + cη * (1 - γ) * j))) :
    ∃ s : Fin 4, 1 / 10 ^ 9 / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤
      ∫ d, (qLearningValue (qLbMDP γ hγ' hγ1)
        (qSampledIterate (qLbMDP γ hγ' hγ1) (fun t ↦ 1 / (1 + cη * (1 - γ) * t)) T
          (fun _ _ ↦ 0) d) s -
        (qLbMDP γ hγ' hγ1).trajectoryExpectedValue (qLbMDP γ hγ' hγ1).optimalGreedyPolicy s) ^ 2
          ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T := by
  obtain ⟨hRT, hTpos, hlog, hT1, -⟩ := qLbv_setup γ hγ hγ1 T hT
  have hg : 0 < 1 - γ := by linarith
  have hg4 : 1 - γ ≤ 1 / 4 := by linarith
  have hD0 : 0 ≤ cη * (1 - γ) := by positivity
  have hDpos : 0 < cη * (1 - γ) := by positivity
  set η : ℕ → ℝ := fun t ↦ 1 / (1 + cη * (1 - γ) * t) with hηdef
  have hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1 := qLbvRate_bounds (cη * (1 - γ)) hD0
  have hid := qLb_one_sub_gamma_p γ hγ'
  have hκ0 : 0 ≤ 1 - γ * qHardP γ := by rw [hid]; positivity
  have hκ13 : 1 - γ * qHardP γ ≤ 1 / 3 := by rw [hid]; linarith
  have hrow := qLbMDP_rowSpec γ hγ' hγ1
  -- split `Σ = κ η_1 + ∑_{j=2}^T κ η_j`
  have hsplit : ∑ j ∈ Finset.Ioc 0 T, (1 - γ * qHardP γ) * η j =
      (1 - γ * qHardP γ) * η 1 + ∑ j ∈ Finset.Ioc 1 T, (1 - γ * qHardP γ) * η j := by
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hT1,
      show Finset.Ioc 0 1 = {1} from Nat.Ioc_succ_singleton 0, Finset.sum_singleton]
  have hη1 : (1 - γ * qHardP γ) * η 1 ≤ 1 / 3 :=
    (mul_le_of_le_one_right hκ0 (hη 1).2).trans hκ13
  have hrest : 1 / 6 < ∑ j ∈ Finset.Ioc 1 T, (1 - γ * qHardP γ) * η j := by
    have : 1 / 2 < ∑ j ∈ Finset.Ioc 0 T, (1 - γ * qHardP γ) * η j := hC
    linarith
  have hrestle : ∑ j ∈ Finset.Ioc 1 T, (1 - γ * qHardP γ) * η j ≤
      (1 - γ * qHardP γ) * (1 / (cη * (1 - γ)) * Real.log T) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (qLbvRate_sum_one (cη * (1 - γ)) hDpos T hT1) hκ0
  have hc8 : cη < 8 * Real.log T := by
    have e : (1 - γ * qHardP γ) * (1 / (cη * (1 - γ)) * Real.log T) =
        4 * Real.log T / (3 * cη) := by
      rw [hid]; field_simp
    have h1 : 1 / 6 < 4 * Real.log T / (3 * cη) := by linarith
    rw [lt_div_iff₀ (by positivity)] at h1
    linarith
  have hPi1 : qLbvProd η (1 - γ * qHardP γ) 1 T ≤ 6 / 7 := by
    have h1 := qLbvProd_le_inv η (1 - γ * qHardP γ) 1 T (fun j ↦ mul_nonneg hκ0 (hη j).1)
      (fun j ↦ (mul_le_of_le_one_right hκ0 (hη j).2).trans (by linarith))
    have h2 : 1 / (1 + ∑ j ∈ Finset.Ioc 1 T, (1 - γ * qHardP γ) * η j) ≤ 6 / 7 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  -- the rate floor `b`
  set b := 5 / 1536 * min (Real.sqrt (η T / (1 - γ))) 1 with hb
  have hm : ∀ t, 1 ≤ t → t ≤ T →
      b ≤ ∫ d, qLbvXiMax γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) t
        ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T := by
    intro t ht1 htT
    refine le_trans ?_ (qLbv_xiMax_lower_rescaled (qLbMDP γ hγ' hγ1) T γ (cη * (1 - γ)) hD0 hD1
      hγ hγ1 hrow t ht1 htT)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply min_le_min_right
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (qLbvRate_anti (cη * (1 - γ)) hD0 t T htT) hg.le
  have hb0 : 0 ≤ b := by
    rw [hb]; apply mul_nonneg (by norm_num)
    exact le_min (Real.sqrt_nonneg _) zero_le_one
  have h5 := qLbv_step5 (qLbMDP γ hγ' hγ1) T γ η hγ hγ1 hη hrow b hT1 hm
  set EV := ∫ d, qLbvAuxValue γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T
    ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T with hEV
  -- `E V̂_T - V⋆(1) ≥ b/(14(1-γ))`
  have hEVlow : b / (14 * (1 - γ)) ≤ EV - 1 / (1 - γ * qHardP γ) := by
    have hw23 : 2 / 3 ≤ γ * qHardP γ := by linarith
    have h17 : (1 : ℝ) / 7 ≤ 1 - qLbvProd η (1 - γ * qHardP γ) 1 T := by linarith
    have h1 : 2 / 3 * b * (1 / 7) ≤ γ * qHardP γ * b * (1 - qLbvProd η (1 - γ * qHardP γ) 1 T) := by
      have h0 := mul_le_mul_of_nonneg_right hw23 hb0
      have := mul_le_mul h0 h17 (by norm_num) (by positivity)
      linarith
    have h2 : 2 / 21 * b ≤ 4 * (1 - γ) / 3 * (EV - 1 / (1 - γ * qHardP γ)) := by
      rw [← hid]; linarith
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hVs : ∀ s, (qLbMDP γ hγ' hγ1).trajectoryExpectedValue
      (qLbMDP γ hγ' hγ1).optimalGreedyPolicy s = qHardValue γ s :=
    fun s ↦ congrFun (qLbMDP_value γ hγ' hγ1) s
  have hout := qLbv_output_ae γ η hγ' hγ1 hη T
  have hE1 : EV - qLbvProd η (1 - γ) 0 T / (1 - γ) ≤
      ∫ d, qLearningValue (qLbMDP γ hγ' hγ1)
        (qSampledIterate (qLbMDP γ hγ' hγ1) η T (fun _ _ ↦ 0) d) 1
        ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T := by
    have := integral_mono_ae (qSampling_integrable (qLbMDP γ hγ' hγ1) T _)
      (qSampling_integrable (qLbMDP γ hγ' hγ1) T _)
      (by filter_upwards [hout] with d hd; exact hd.2.2)
    rw [integral_sub (qSampling_integrable _ T _) (integrable_const _)] at this
    simpa [integral_const] using this
  have hE3 : ∫ d, qLearningValue (qLbMDP γ hγ' hγ1)
        (qSampledIterate (qLbMDP γ hγ' hγ1) η T (fun _ _ ↦ 0) d) 3
        ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T = (1 - qLbvProd η (1 - γ) 0 T) / (1 - γ) := by
    have : ∫ d, qLearningValue (qLbMDP γ hγ' hγ1)
        (qSampledIterate (qLbMDP γ hγ' hγ1) η T (fun _ _ ↦ 0) d) 3
        ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T =
        ∫ _d, (1 - qLbvProd η (1 - γ) 0 T) / (1 - γ) ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T :=
      integral_congr_ae (by filter_upwards [hout] with d hd; exact hd.2.1)
    rw [this]; simp
  have hfinal := qLbv_caseC_final (1 - γ) T (Real.log T) cη b hg hg4 hRT hlog hcη hc8
    (le_of_eq (by rw [hb, hηdef]))
  set B := b / (28 * (1 - γ)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  set I1 := ∫ d, qLearningValue (qLbMDP γ hγ' hγ1)
    (qSampledIterate (qLbMDP γ hγ' hγ1) η T (fun _ _ ↦ 0) d) 1
    ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T with hI1
  have hsum : 2 * B ≤ (I1 - 1 / (1 - γ * qHardP γ)) + (1 / (1 - γ) -
      (1 - qLbvProd η (1 - γ) 0 T) / (1 - γ)) := by
    have e : 1 / (1 - γ) - (1 - qLbvProd η (1 - γ) 0 T) / (1 - γ) =
        qLbvProd η (1 - γ) 0 T / (1 - γ) := by field_simp; ring
    have e2 : 2 * B = b / (14 * (1 - γ)) := by rw [hBdef]; field_simp; ring
    rw [e, e2]
    linarith
  rcases le_or_gt B (I1 - 1 / (1 - γ * qHardP γ)) with h1 | h1
  · refine ⟨1, ?_⟩
    have hsq := qLb_sq_integral_le (qLbMDP γ hγ' hγ1) T
      (fun d ↦ qLearningValue (qLbMDP γ hγ' hγ1)
        (qSampledIterate (qLbMDP γ hγ' hγ1) η T (fun _ _ ↦ 0) d) 1)
      ((qLbMDP γ hγ' hγ1).trajectoryExpectedValue (qLbMDP γ hγ' hγ1).optimalGreedyPolicy 1)
    rw [hVs 1] at hsq ⊢
    simp only [qHardValue, show ¬((1 : Fin 4) = 0) by decide,
      show ¬((1 : Fin 4) = 3) by decide, ↓reduceIte] at hsq ⊢
    exact hfinal.trans ((pow_le_pow_left₀ hB0 h1 2).trans hsq)
  · refine ⟨3, ?_⟩
    have hsq := qLb_sq_integral_le (qLbMDP γ hγ' hγ1) T
      (fun d ↦ qLearningValue (qLbMDP γ hγ' hγ1)
        (qSampledIterate (qLbMDP γ hγ' hγ1) η T (fun _ _ ↦ 0) d) 3)
      ((qLbMDP γ hγ' hγ1).trajectoryExpectedValue (qLbMDP γ hγ' hγ1).optimalGreedyPolicy 3)
    rw [hVs 3, hE3] at hsq
    rw [hVs 3]
    simp only [qHardValue, show ¬((3 : Fin 4) = 0) by decide, ↓reduceIte] at hsq ⊢
    have h3 : B ≤ 1 / (1 - γ) - (1 - qLbvProd η (1 - γ) 0 T) / (1 - γ) := by linarith
    have h4 : B ^ 2 ≤ ((1 - qLbvProd η (1 - γ) 0 T) / (1 - γ) - 1 / (1 - γ)) ^ 2 := by
      rw [show ((1 - qLbvProd η (1 - γ) 0 T) / (1 - γ) - 1 / (1 - γ)) ^ 2 =
        (1 / (1 - γ) - (1 - qLbvProd η (1 - γ) 0 T) / (1 - γ)) ^ 2 by ring]
      exact pow_le_pow_left₀ hB0 h3 2
    exact hfinal.trans (h4.trans hsq)

/-- Theorem 4.7, case (i) (rescaled linear learning rates `η_t = 1/(1 + c_η(1-γ)t)`), with
`c₃ = 16`, `c_lb = 10⁻⁹`, both independent of `c_η`; the witness MDP `qLbMDP γ` depends only on `γ`. -/
theorem qLb_thm47_rescaledLinear : ∃ c₃ c_lb : ℝ, 0 < c₃ ∧ 0 < c_lb ∧
    ∀ γ : ℝ, 3 / 4 ≤ γ → γ < 1 → ∀ T : ℕ, c₃ / (1 - γ) ^ 2 ≤ T → ∀ cη : ℝ, 0 < cη →
    ∃ M : DiscountedMDP (Fin 4) Bool, M.discount = γ ∧ ∃ s : Fin 4,
      c_lb / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤
        ∫ d, (qLearningValue M (qSampledIterate M (fun t ↦ 1 / (1 + cη * (1 - γ) * t)) T
          (fun _ _ ↦ 0) d) s - M.trajectoryExpectedValue M.optimalGreedyPolicy s) ^ 2
          ∂qSamplingLaw M T := by
  refine ⟨16, 1 / 10 ^ 9, by norm_num, by norm_num, ?_⟩
  intro γ hγ hγ1 T hT cη hcη
  have hγ' : (1 : ℝ) / 4 < γ := by linarith
  refine ⟨qLbMDP γ hγ' hγ1, rfl, ?_⟩
  rcases lt_or_ge 1 (cη * (1 - γ)) with hA | hD1
  · exact ⟨2, qLbv_caseAB γ hγ hγ' hγ1 T hT cη hcη (Or.inl hA)⟩
  rcases le_or_gt (∑ j ∈ Finset.Ioc 0 T, (1 - γ * qHardP γ) * (1 / (1 + cη * (1 - γ) * j)))
    (1 / 2) with hB | hC
  · exact ⟨2, qLbv_caseAB γ hγ hγ' hγ1 T hT cη hcη (Or.inr hB)⟩
  · exact qLbv_caseC γ hγ hγ' hγ1 T hT cη hcη hD1 hC

/-- Theorem 4.7, both printed schedules: (i) rescaled linear `η_t = 1/(1 + c_η(1-γ)t)`, `c_η > 0`,
or (ii) constant `η_t ≡ η₀ ∈ (0,1)`. Combines `qLb_thm47_rescaledLinear` and `qLb_thm47_constantRate`
(`c₃ = max = 16`, `c_lb = min(10⁻⁹, e^{-16}) = 10⁻⁹`). -/
theorem qLb_thm47 : ∃ c₃ c_lb : ℝ, 0 < c₃ ∧ 0 < c_lb ∧
    ∀ γ : ℝ, 3 / 4 ≤ γ → γ < 1 → ∀ T : ℕ, c₃ / (1 - γ) ^ 2 ≤ T →
    ∀ η : ℕ → ℝ,
      ((∃ cη : ℝ, 0 < cη ∧ ∀ t : ℕ, η t = 1 / (1 + cη * (1 - γ) * t)) ∨
        (∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧ ∀ t : ℕ, η t = η₀)) →
      ∃ M : DiscountedMDP (Fin 4) Bool, M.discount = γ ∧ ∃ s : Fin 4,
        c_lb / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤
          ∫ d, (qLearningValue M (qSampledIterate M η T (fun _ _ ↦ 0) d) s -
            M.trajectoryExpectedValue M.optimalGreedyPolicy s) ^ 2 ∂qSamplingLaw M T := by
  obtain ⟨a₃, alb, ha₃, halb, hi⟩ := qLb_thm47_rescaledLinear
  obtain ⟨b₃, blb, hb₃, hblb, hii⟩ := qLb_thm47_constantRate
  refine ⟨max a₃ b₃, min alb blb, lt_max_of_lt_left ha₃, lt_min halb hblb, ?_⟩
  intro γ hγ hγ1 T hT η hη
  have hg2 : 0 < (1 - γ) ^ 2 := by
    have : 0 < 1 - γ := by linarith
    positivity
  have hTa : a₃ / (1 - γ) ^ 2 ≤ T :=
    le_trans (div_le_div_of_nonneg_right (le_max_left _ _) hg2.le) hT
  have hTb : b₃ / (1 - γ) ^ 2 ≤ T :=
    le_trans (div_le_div_of_nonneg_right (le_max_right _ _) hg2.le) hT
  have hX : 0 ≤ (1 - γ) ^ 4 * T * Real.log T ^ 2 := by positivity
  rcases hη with ⟨cη, hcη, hηeq⟩ | ⟨η₀, h0, h1, hηeq⟩
  · have hfun : η = fun t : ℕ ↦ 1 / (1 + cη * (1 - γ) * t) := funext hηeq
    subst hfun
    obtain ⟨M, hM, s, hs⟩ := hi γ hγ hγ1 T hTa cη hcη
    exact ⟨M, hM, s, le_trans (div_le_div_of_nonneg_right (min_le_left _ _) hX) hs⟩
  · have hfun : η = fun _ : ℕ ↦ η₀ := funext hηeq
    subst hfun
    obtain ⟨M, hM, s, hs⟩ := hii γ hγ hγ1 T hTb η₀ h0 h1
    exact ⟨M, hM, s, le_trans (div_le_div_of_nonneg_right (min_le_right _ _) hX) hs⟩

end StatisticalRL.QLearning

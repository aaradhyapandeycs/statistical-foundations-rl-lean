import Formalization.ModelFree.QLearningLowerBoundModerate
import Formalization.ModelFree.QLearningLowerBoundState2

/-!
# Theorem 4.7 (`thm:LB-example-Q-generative`), case (ii): constant learning rates

`chapters/generative_model_model_free.tex:969–982`, proof (Appendix C) `:2707–3944`.
For every `γ ∈ [3/4,1)`, `T ≥ 16/(1-γ)²` and constant rate `η ∈ (0,1)`, synchronous Q-learning
from `Q₀ = 0` on `qLbMDP γ` (4 states, 2 actions) satisfies
`max_s E[(V_T(s) - V⋆(s))²] ≥ e^{-16}/((1-γ)⁴ T log² T)`.
Regimes: (A) `η ≤ 4/((1-γ)T)`, bias of state 2 (Step 3); (B) `η ≥ 1/((1-γ)²T)`, variance of
state 2 (Step 4); (C) otherwise, over-estimation at state 1 together with state 3 (Step 5).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

theorem qLb_valid_ae (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) (N : ℕ) :
    ∀ᵐ d ∂qSamplingLaw (qLbMDP γ hγ hγ1) N,
      qLbValid (qLbMDP γ hγ hγ1) (qSamplesExtend (qLbMDP γ hγ hγ1) N d) N := by
  filter_upwards [qLb_support_ae (qLbMDP γ hγ hγ1) N] with d hd
  intro k hk1 hkN s a
  rw [qSamplesExtend_coord _ N k hk1 hkN]
  exact hd ((s, a), ⟨k - 1, by omega⟩)

/-- The Q-learning output values on `qLbMDP`, almost surely. -/
theorem qLb_output_ae (γ η : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) (T : ℕ) :
    ∀ᵐ d ∂qSamplingLaw (qLbMDP γ hγ hγ1) T,
      qLearningValue (qLbMDP γ hγ hγ1)
          (qSampledIterate (qLbMDP γ hγ hγ1) (fun _ ↦ η) T (fun _ _ ↦ 0) d) 2 =
        qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) T d) T ∧
      qLearningValue (qLbMDP γ hγ hγ1)
          (qSampledIterate (qLbMDP γ hγ hγ1) (fun _ ↦ η) T (fun _ _ ↦ 0) d) 3 =
        (1 - (1 - η * (1 - γ)) ^ T) / (1 - γ) ∧
      qLbAuxValue γ η (qSamplesExtend (qLbMDP γ hγ hγ1) T d) T - (1 - η * (1 - γ)) ^ T / (1 - γ) ≤
        qLearningValue (qLbMDP γ hγ hγ1)
          (qSampledIterate (qLbMDP γ hγ hγ1) (fun _ ↦ η) T (fun _ _ ↦ 0) d) 1 := by
  filter_upwards [qLb_valid_ae γ hγ hγ1 T] with d hd
  obtain ⟨-, -, h2t, h3t, h3f, h2f, h1⟩ :=
    qLb_pathwise γ η hγ hγ1 hη0 hη1 (qSamplesExtend (qLbMDP γ hγ hγ1) T d) T hd T le_rfl
  have hnn := qLbRun_nonneg γ η hγ hγ1 hη0 hη1 (qSamplesExtend (qLbMDP γ hγ hγ1) T d) T
  change qLearningValue (qLbMDP γ hγ hγ1) (qLbRun γ η hγ hγ1 (qSamplesExtend _ T d) T) 2 = _ ∧
    qLearningValue (qLbMDP γ hγ hγ1) (qLbRun γ η hγ hγ1 (qSamplesExtend _ T d) T) 3 = _ ∧
    _ ≤ qLearningValue (qLbMDP γ hγ hγ1) (qLbRun γ η hγ hγ1 (qSamplesExtend _ T d) T) 1
  simp only [qLearningValue_bool]
  refine ⟨?_, ?_, ?_⟩
  · rw [h2t, max_eq_left (hnn 2 false), h2f]
  · rw [h3t, max_eq_left (hnn 3 false), h3f]
  · unfold qLbAuxValue
    rw [← max_sub_sub_right]
    exact max_le_max (h1 false) (h1 true)

/-- `exp(-16) ≤ 9/26214400`. -/
theorem qLb_exp_neg16_le : Real.exp (-16) ≤ 9 / 26214400 := by
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h16 : Real.exp 16 = Real.exp 1 ^ 16 := by rw [← Real.exp_nat_mul]; norm_num
  have : (26214400 / 9 : ℝ) ≤ Real.exp 16 := by
    rw [h16]
    calc (26214400 / 9 : ℝ) ≤ 2.7 ^ 16 := by norm_num
      _ ≤ Real.exp 1 ^ 16 := pow_le_pow_left₀ (by norm_num) he 16
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 16) (by norm_num)]
  linarith

theorem qLb_exp_neg16_le_30 : Real.exp (-16) ≤ 1 / 30 := by
  have := qLb_exp_neg16_le; linarith

/-- The arithmetic of `qLb_lemma415`, isolated. -/
theorem qLb_b_lower (γ η : ℝ) (T : ℕ) (hγ1 : γ < 1) (hRT : 16 ≤ (1 - γ) ^ 2 * T)
    (hlog : 1 ≤ Real.log T) (h4 : 4 < η * (1 - γ) * T) :
    1 / 320 / (Real.sqrt ((1 - γ) ^ 2 * T) * Real.log T) ≤
      5 / 1536 * min (Real.sqrt (η / (1 - γ))) 1 := by
  have hg : 0 < 1 - γ := by linarith
  have hTpos : (0 : ℝ) < T := by
    by_contra h; push_neg at h; nlinarith [sq_nonneg (1 - γ)]
  set R := Real.sqrt ((1 - γ) ^ 2 * T) with hR
  have hR4 : 4 ≤ R := by
    rw [hR, show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hRT
  have hR2 : R ^ 2 = (1 - γ) ^ 2 * T := Real.sq_sqrt (by positivity)
  have hRL : 1 ≤ R * Real.log T := by
    have := mul_le_mul hR4 hlog zero_le_one (by linarith)
    linarith
  have hη0 : 0 < η := by
    by_contra h; push_neg at h
    have : η * (1 - γ) * T ≤ 0 := by
      have := mul_nonpos_of_nonpos_of_nonneg h hg.le
      exact mul_nonpos_of_nonpos_of_nonneg this hTpos.le
    linarith
  have hsx : 2 / R ≤ Real.sqrt (η / (1 - γ)) := by
    rw [Real.le_sqrt (by positivity) (by positivity), div_pow, hR2,
      div_le_div_iff₀ (by positivity) hg]
    have := mul_lt_mul_of_pos_left h4 hg
    have e : η * ((1 - γ) ^ 2 * T) = (1 - γ) * (η * (1 - γ) * T) := by ring
    nlinarith
  have hinv : 1 / (R * Real.log T) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hRL
  have hinv2 : 1 / (R * Real.log T) ≤ 2 / R := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ R)
    linarith
  have hmin : 1 / (R * Real.log T) ≤ min (Real.sqrt (η / (1 - γ))) 1 :=
    le_min (hinv2.trans hsx) hinv
  have e : 1 / 320 / (R * Real.log T) = 1 / 320 * (1 / (R * Real.log T)) := by ring
  rw [e]
  have h0 : 0 ≤ 1 / (R * Real.log T) := by positivity
  have := mul_le_mul_of_nonneg_left hmin (by norm_num : (0 : ℝ) ≤ 5 / 1536)
  linarith

/-! ### Scalar parts of the three regimes -/

/-- Common consequences of `T ≥ 16/(1-γ)²`, `γ ∈ [3/4,1)`. -/
theorem qLb_T_facts (γ : ℝ) (T : ℕ) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1)
    (hT : 16 / (1 - γ) ^ 2 ≤ T) :
    16 ≤ (1 - γ) ^ 2 * T ∧ (0 : ℝ) < T ∧ 1 ≤ Real.log T ∧
      16 * (1 - γ) ^ 2 ≤ (1 - γ) ^ 4 * T * Real.log T ^ 2 ∧
      (1 - γ) ^ 4 * T ≤ (1 - γ) ^ 4 * T * Real.log T ^ 2 := by
  have hg : 0 < 1 - γ := by linarith
  have hg2 : 0 < (1 - γ) ^ 2 := by positivity
  have hRT : 16 ≤ (1 - γ) ^ 2 * T := by rw [div_le_iff₀ hg2] at hT; linarith
  have hg16 : (1 - γ) ^ 2 ≤ 1 / 16 := by nlinarith
  have hT256 : (256 : ℝ) ≤ T := by nlinarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hlog : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    have := Real.exp_one_lt_d9
    linarith
  have hl2 : 1 ≤ Real.log T ^ 2 := by nlinarith
  have h4 : 0 ≤ (1 - γ) ^ 4 * T := by positivity
  refine ⟨hRT, hTpos, hlog, ?_, ?_⟩
  · have e : (1 - γ) ^ 4 * T = (1 - γ) ^ 2 * ((1 - γ) ^ 2 * T) := by ring
    have h5 : 16 * (1 - γ) ^ 2 ≤ (1 - γ) ^ 4 * T := by
      rw [e]; nlinarith
    nlinarith
  · nlinarith

theorem qLb_rho_bounds (γ η : ℝ) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hη0 : 0 < η) (hη1 : η < 1) :
    0 ≤ 1 - η * (4 * (1 - γ) / 3) ∧ 2 / 3 ≤ 1 - η * (4 * (1 - γ) / 3) ∧
      1 - η * (4 * (1 - γ) / 3) ≤ 1 ∧ 1 - η ≤ 1 - η * (4 * (1 - γ) / 3) := by
  have hy : η * (4 * (1 - γ) / 3) ≤ 1 / 3 := by nlinarith
  have hy0 : 0 ≤ η * (4 * (1 - γ) / 3) := by
    have : 0 ≤ 1 - γ := by linarith
    positivity
  have hy1 : η * (4 * (1 - γ) / 3) ≤ η := by nlinarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem qLb_rho_tail (ρ : ℝ) (T τ₀ : ℕ) (hρ0 : 0 ≤ ρ) (hρ23 : 2 / 3 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρT : ρ ^ T ≤ 1 / 100) (hT1 : 1 ≤ T) (hτ3 : T - 1 ≤ 2 * (T - τ₀)) :
    ρ ^ (2 * (T - τ₀)) ≤ 3 / 200 ∧ ρ ^ (T - τ₀) ≤ 1 / 2 := by
  have hρTm1 : ρ ^ (T - 1) ≤ 3 / 200 := by
    have e : ρ ^ T = ρ ^ (T - 1) * ρ := by rw [← pow_succ, show T - 1 + 1 = T by omega]
    have h0 : 0 ≤ ρ ^ (T - 1) := pow_nonneg hρ0 _
    have : ρ ^ (T - 1) * (2 / 3) ≤ ρ ^ (T - 1) * ρ := mul_le_mul_of_nonneg_left hρ23 h0
    linarith
  have h3 : ρ ^ (2 * (T - τ₀)) ≤ 3 / 200 := (pow_le_pow_of_le_one hρ0 hρ1 hτ3).trans hρTm1
  refine ⟨h3, ?_⟩
  have h2 : ρ ^ (2 * (T - τ₀)) = (ρ ^ (T - τ₀)) ^ 2 := by rw [pow_mul']
  have h0 : 0 ≤ ρ ^ (T - τ₀) := pow_nonneg hρ0 _
  nlinarith

/-- Step 3 (small rates), scalar part: the squared bias of state 2 dominates. -/
theorem qLb_caseA_scalar (γ η : ℝ) (T : ℕ) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hη0 : 0 < η)
    (hη1 : η < 1) (hA : η * (1 - γ) * T ≤ 4)
    (hD16 : 16 * (1 - γ) ^ 2 ≤ (1 - γ) ^ 4 * T * Real.log T ^ 2)
    (hDpos : 0 < (1 - γ) ^ 4 * T * Real.log T ^ 2) :
    Real.exp (-16) / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤
      ((1 - η * (4 * (1 - γ) / 3)) ^ T * (3 / (4 * (1 - γ)))) ^ 2 := by
  have hg : 0 < 1 - γ := by linarith
  set ρ := 1 - η * (4 * (1 - γ) / 3) with hρ
  have hy : η * (4 * (1 - γ) / 3) ≤ 1 / 3 := by nlinarith
  have hρ0 : 0 < ρ := by rw [hρ]; nlinarith
  have hρT : Real.exp (-8) ≤ ρ ^ T := by
    have hlogρ : -(3 / 2) * (η * (4 * (1 - γ) / 3)) ≤ Real.log ρ := by
      have := Real.one_sub_inv_le_log_of_pos hρ0
      have hinv : ρ⁻¹ ≤ 1 + 3 / 2 * (η * (4 * (1 - γ) / 3)) := by
        rw [inv_le_iff_one_le_mul₀ hρ0, hρ]
        have hy0 : 0 ≤ η * (4 * (1 - γ) / 3) := by positivity
        nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy)]
      linarith
    have hTy : (T : ℝ) * (η * (4 * (1 - γ) / 3)) ≤ 16 / 3 := by nlinarith
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have h1 : (-8 : ℝ) ≤ T * Real.log ρ := by nlinarith
    calc Real.exp (-8) ≤ Real.exp (T * Real.log ρ) := Real.exp_le_exp.mpr h1
      _ = ρ ^ T := by rw [Real.exp_nat_mul, Real.exp_log hρ0]
  have hgoal : Real.exp (-16) * (9 / (16 * (1 - γ) ^ 2)) ≤ (ρ ^ T * (3 / (4 * (1 - γ)))) ^ 2 := by
    rw [mul_pow, show Real.exp (-16) = Real.exp (-8) ^ 2 by rw [← Real.exp_nat_mul]; norm_num]
    have : (3 / (4 * (1 - γ))) ^ 2 = 9 / (16 * (1 - γ) ^ 2) := by field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hρT 2) (by positivity)
  have hlb : Real.exp (-16) / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤
      Real.exp (-16) * (9 / (16 * (1 - γ) ^ 2)) := by
    rw [div_le_iff₀ hDpos]
    have h1 : 9 / (16 * (1 - γ) ^ 2) * (16 * (1 - γ) ^ 2) ≤
        9 / (16 * (1 - γ) ^ 2) * ((1 - γ) ^ 4 * T * Real.log T ^ 2) :=
      mul_le_mul_of_nonneg_left hD16 (by positivity)
    rw [show 9 / (16 * (1 - γ) ^ 2) * (16 * (1 - γ) ^ 2) = 9 by field_simp] at h1
    have he := Real.exp_pos (-16)
    have := mul_le_mul_of_nonneg_left h1 he.le
    nlinarith
  linarith

theorem qLb_caseB_final (γ η aT : ℝ) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hη0 : 0 < η)
    (h : η ^ 2 * (4 * γ - 1) * 81 / (1600 * (1 - γ)) * (197 / 200) ≤ aT * (8 * η * (1 - γ) / 3)) :
    η ≤ aT * (30 * (1 - γ) ^ 2) := by
  have hg : 0 < 1 - γ := by linarith
  have h1 : η ^ 2 * (4 * γ - 1) * 81 * 197 ≤ aT * (8 * η * (1 - γ) / 3) * (1600 * (1 - γ) * 200) := by
    have e : η ^ 2 * (4 * γ - 1) * 81 / (1600 * (1 - γ)) * (197 / 200) =
        η ^ 2 * (4 * γ - 1) * 81 * 197 / (1600 * (1 - γ) * 200) := by field_simp
    rw [e, div_le_iff₀ (by positivity)] at h
    exact h
  have h2 : η ^ 2 * (2 * 81 * 197) ≤ η ^ 2 * (4 * γ - 1) * 81 * 197 := by
    have := mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) ≤ 4 * γ - 1) (sq_nonneg η)
    linarith
  have e3 : aT * (8 * η * (1 - γ) / 3) * (1600 * (1 - γ) * 200) =
      η * (aT * (1 - γ) ^ 2 * (8 * 1600 * 200 / 3)) := by ring
  rw [e3] at h1
  have h4 : η * (2 * 81 * 197) ≤ aT * (1 - γ) ^ 2 * (8 * 1600 * 200 / 3) := by
    have e4 : η ^ 2 * (2 * 81 * 197) = η * (η * (2 * 81 * 197)) := by ring
    have : η * (η * (2 * 81 * 197)) ≤ η * (aT * (1 - γ) ^ 2 * (8 * 1600 * 200 / 3)) := by
      linarith
    exact le_of_mul_le_mul_left this hη0
  have e5 : aT * (30 * (1 - γ) ^ 2) = aT * (1 - γ) ^ 2 * 30 := by ring
  rw [e5]
  linarith

/-- Step 4 (large rates), scalar part: the variance recursion of state 2. -/
theorem qLb_caseB_scalar (γ η ρ c Vh : ℝ) (T : ℕ) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1)
    (hη0 : 0 < η) (hη1 : η < 1) (hρ : ρ = 1 - η * (4 * (1 - γ) / 3))
    (hc : c = η ^ 2 * ((4 * γ - 1) * (1 - γ) / 9)) (hVh : Vh = 3 / (4 * (1 - γ)))
    (hB : 1 ≤ η * ((1 - γ) ^ 2 * T)) (hρT : ρ ^ T ≤ 1 / 100) (hT1 : 1 ≤ T)
    (hD1 : (1 - γ) ^ 4 * T ≤ (1 - γ) ^ 4 * T * Real.log T ^ 2)
    (a mm : ℕ → ℝ) (ha0 : ∀ t, 0 ≤ a t)
    (hstep : ∀ t, t + 1 ≤ T → ρ ^ 2 * a t + c * mm t ^ 2 ≤ a (t + 1))
    (hmean : ∀ t, t ≤ T → Vh - mm t = ρ ^ t * Vh) :
    Real.exp (-16) / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤ a T := by
  have hg : 0 < 1 - γ := by linarith
  obtain ⟨-, hρ23, hρ1, -⟩ := qLb_rho_bounds γ η hγ hγ1 hη0 hη1
  rw [← hρ] at hρ23 hρ1
  have hρ0 : 0 < ρ := by linarith
  have hVh0 : 0 < Vh := by rw [hVh]; positivity
  set τ₀ := (T + 1) / 2 with hτ₀
  have hτ2 : T ≤ 2 * τ₀ := by omega
  have hτ3 : T - 1 ≤ 2 * (T - τ₀) := by omega
  have hρtail := (qLb_rho_tail ρ T τ₀ hρ0.le hρ23 hρ1 hρT hT1 hτ3).1
  have hρτ : ρ ^ τ₀ ≤ 1 / 10 := by
    have h1 : ρ ^ (2 * τ₀) ≤ ρ ^ T := pow_le_pow_of_le_one hρ0.le hρ1 hτ2
    have h2 : ρ ^ (2 * τ₀) = (ρ ^ τ₀) ^ 2 := by rw [pow_mul']
    have h0 : 0 ≤ ρ ^ τ₀ := pow_nonneg hρ0.le _
    nlinarith
  have hc0 : 0 ≤ c := by rw [hc]; have : 0 ≤ (4 * γ - 1) * (1 - γ) := by nlinarith
                         positivity
  set K := c * (81 / 100 * Vh ^ 2) with hK
  have hmmK : ∀ t, τ₀ ≤ t → t ≤ T → K ≤ c * mm t ^ 2 := by
    intro t ht1 ht2
    have h1 := hmean t ht2
    have h2 : ρ ^ t ≤ ρ ^ τ₀ := pow_le_pow_of_le_one hρ0.le hρ1 ht1
    have h3 : 9 / 10 * Vh ≤ mm t := by
      have : ρ ^ t * Vh ≤ 1 / 10 * Vh := mul_le_mul_of_nonneg_right (h2.trans hρτ) hVh0.le
      linarith
    have h4 : 81 / 100 * Vh ^ 2 ≤ mm t ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) h3 2
      nlinarith
    exact mul_le_mul_of_nonneg_left h4 hc0
  have h1ρ2 : 0 ≤ 1 - ρ ^ 2 := by
    have : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ0.le hρ1
    linarith
  have hind : ∀ j, τ₀ + j ≤ T → K * (1 - ρ ^ (2 * j)) ≤ a (τ₀ + j) * (1 - ρ ^ 2) := by
    intro j
    induction j with
    | zero => intro _; simp only [mul_zero, pow_zero, sub_self]; exact mul_nonneg (ha0 _) h1ρ2
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hs := hstep (τ₀ + j) (by omega)
      have hk := hmmK (τ₀ + j) (by omega) (by omega)
      rw [show τ₀ + (j + 1) = τ₀ + j + 1 by ring]
      have e : ρ ^ (2 * (j + 1)) = ρ ^ 2 * ρ ^ (2 * j) := by
        rw [show 2 * (j + 1) = 2 + 2 * j by ring, pow_add]
      rw [e]
      have h5 := mul_le_mul_of_nonneg_right hs h1ρ2
      have h6 := mul_le_mul_of_nonneg_left ih' (sq_nonneg ρ)
      have h7 := mul_le_mul_of_nonneg_right hk h1ρ2
      nlinarith
  have hfin := hind (T - τ₀) (by omega)
  rw [show τ₀ + (T - τ₀) = T by omega] at hfin
  have hK0 : 0 ≤ K := by positivity
  have hK1 : K * (197 / 200) ≤ a T * (1 - ρ ^ 2) := by
    have : K * (197 / 200) ≤ K * (1 - ρ ^ (2 * (T - τ₀))) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    linarith
  have h1ρ2' : 1 - ρ ^ 2 ≤ 8 * η * (1 - γ) / 3 :=
    calc 1 - ρ ^ 2 = (1 - ρ) * (1 + ρ) := by ring
      _ ≤ (1 - ρ) * 2 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = 8 * η * (1 - γ) / 3 := by rw [hρ]; ring
  have hK2 : K * (197 / 200) ≤ a T * (8 * η * (1 - γ) / 3) :=
    hK1.trans (mul_le_mul_of_nonneg_left h1ρ2' (ha0 T))
  have hKc : K = η ^ 2 * (4 * γ - 1) * 81 / (1600 * (1 - γ)) := by
    rw [hK, hc, hVh]; field_simp; ring
  rw [hKc] at hK2
  have haT := qLb_caseB_final γ η (a T) hγ hγ1 hη0 hK2
  have hDpos : 0 < (1 - γ) ^ 4 * T * Real.log T ^ 2 := by
    have : (0 : ℝ) < (1 - γ) ^ 4 * T := by
      have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
      positivity
    linarith
  rw [div_le_iff₀ hDpos]
  have he : Real.exp (-16) ≤ 1 / 30 := qLb_exp_neg16_le_30
  have s1 : a T * ((1 - γ) ^ 4 * T) ≤ a T * ((1 - γ) ^ 4 * T * Real.log T ^ 2) :=
    mul_le_mul_of_nonneg_left hD1 (ha0 T)
  have s2 : η * ((1 - γ) ^ 2 * T) ≤ a T * (30 * (1 - γ) ^ 2) * ((1 - γ) ^ 2 * T) :=
    mul_le_mul_of_nonneg_right haT (by positivity)
  have e : a T * (30 * (1 - γ) ^ 2) * ((1 - γ) ^ 2 * T) = 30 * (a T * ((1 - γ) ^ 4 * T)) := by ring
  linarith only [he, s1, s2, e, hB]

/-- Step 5.5 (moderate rates), scalar part: one of states 1 and 3 has a large squared mean
error. -/
theorem qLb_caseC_scalar (γ b EV Vh I1 I3 lamT r w : ℝ) (T : ℕ) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1)
    (hb0 : 0 ≤ b) (hr : r ≤ 1 / 2) (hw : w = 4 * (1 - γ) / 3)
    (h5 : b * (1 - r) ≤ w * (EV - Vh))
    (hE1 : EV - lamT / (1 - γ) ≤ I1) (hE3 : I3 = (1 - lamT) / (1 - γ))
    (hRT : 16 ≤ (1 - γ) ^ 2 * T) (hlog : 1 ≤ Real.log T)
    (hbl : 1 / 320 / (Real.sqrt ((1 - γ) ^ 2 * T) * Real.log T) ≤ b) :
    Real.exp (-16) / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤ (I1 - Vh) ^ 2 ∨
      Real.exp (-16) / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤ (I3 - 1 / (1 - γ)) ^ 2 := by
  have hg : 0 < 1 - γ := by linarith
  have hTpos : (0 : ℝ) < T := by
    by_contra h; push_neg at h; nlinarith [sq_nonneg (1 - γ)]
  set D := (1 - γ) ^ 4 * T * Real.log T ^ 2 with hD
  have hDpos : 0 < D := by
    have : 0 < Real.log T := by linarith
    positivity
  have hD3 : 3 * b / (8 * (1 - γ)) ≤ EV - Vh := by
    have h6 : b / 2 ≤ 4 * (1 - γ) / 3 * (EV - Vh) := by
      rw [← hw]
      have : b / 2 ≤ b * (1 - r) := by nlinarith
      linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  set B := 3 * b / (16 * (1 - γ)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hBlb : Real.exp (-16) / D ≤ B ^ 2 := by
    set R := Real.sqrt ((1 - γ) ^ 2 * T) with hR
    have hR2 : R ^ 2 = (1 - γ) ^ 2 * T := Real.sq_sqrt (by positivity)
    have hR0 : 0 < R := Real.sqrt_pos.mpr (by positivity)
    have hl : 0 < Real.log T := by linarith
    have hB1 : 3 * (1 / 320 / (R * Real.log T)) / (16 * (1 - γ)) ≤ B := by
      rw [hBdef]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have hB2 : (3 * (1 / 320 / (R * Real.log T)) / (16 * (1 - γ))) ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (by positivity) hB1 2
    have e : (3 * (1 / 320 / (R * Real.log T)) / (16 * (1 - γ))) ^ 2 = 9 / 26214400 / D := by
      have : D = R ^ 2 * Real.log T ^ 2 * (1 - γ) ^ 2 := by rw [hD, hR2]; ring
      rw [this]
      field_simp
      ring
    rw [e] at hB2
    have : Real.exp (-16) / D ≤ 9 / 26214400 / D :=
      div_le_div_of_nonneg_right qLb_exp_neg16_le hDpos.le
    linarith
  have hsum : 2 * B ≤ (I1 - Vh) + (1 / (1 - γ) - I3) := by
    rw [hE3]
    have h2B : 2 * B = 3 * b / (8 * (1 - γ)) := by rw [hBdef]; field_simp; ring
    have e : 1 / (1 - γ) - (1 - lamT) / (1 - γ) = lamT / (1 - γ) := by field_simp; ring
    rw [h2B, e]
    linarith
  rcases le_or_gt B (I1 - Vh) with h1 | h1
  · left
    exact hBlb.trans (pow_le_pow_left₀ hB0 h1 2)
  · right
    have h3 : B ≤ 1 / (1 - γ) - I3 := by linarith
    have : B ^ 2 ≤ (I3 - 1 / (1 - γ)) ^ 2 := by
      rw [show (I3 - 1 / (1 - γ)) ^ 2 = (1 / (1 - γ) - I3) ^ 2 by ring]
      exact pow_le_pow_left₀ hB0 h3 2
    exact hBlb.trans this

/-! ### Assembly -/

/-- Theorem 4.7, case (ii) (constant learning rates), with `c₃ = 16`, `c_lb = e^{-16}`; the
witness MDP `qLbMDP γ` depends only on `γ`. -/
theorem qLb_thm47_constantRate : ∃ c₃ c_lb : ℝ, 0 < c₃ ∧ 0 < c_lb ∧
    ∀ γ : ℝ, 3 / 4 ≤ γ → γ < 1 → ∀ T : ℕ, c₃ / (1 - γ) ^ 2 ≤ T →
    ∀ η : ℝ, 0 < η → η < 1 →
    ∃ M : DiscountedMDP (Fin 4) Bool, M.discount = γ ∧ ∃ s : Fin 4,
      c_lb / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤
        ∫ d, (qLearningValue M (qSampledIterate M (fun _ ↦ η) T (fun _ _ ↦ 0) d) s -
          M.trajectoryExpectedValue M.optimalGreedyPolicy s) ^ 2 ∂qSamplingLaw M T := by
  refine ⟨16, Real.exp (-16), by norm_num, Real.exp_pos _, ?_⟩
  intro γ hγ hγ1 T hT η hη0 hη1
  have hγ' : (1 : ℝ) / 4 < γ := by linarith
  refine ⟨qLbMDP γ hγ' hγ1, rfl, ?_⟩
  obtain ⟨hRT, hTpos, hlog, hD16, hD1⟩ := qLb_T_facts γ T hγ hγ1 hT
  have hg : 0 < 1 - γ := by linarith
  have hDpos : 0 < (1 - γ) ^ 4 * T * Real.log T ^ 2 := by
    have : 0 < 16 * (1 - γ) ^ 2 := by positivity
    linarith
  have hT1 : 1 ≤ T := by
    by_contra h; push_neg at h
    have : T = 0 := by omega
    rw [this] at hTpos; simp at hTpos
  have hpv := qLb_gamma_sq_p_var γ hγ'
  have hVh := qLb_vstar_eq γ hγ' hγ1
  have hid : 1 - γ * qHardP γ = 4 * (1 - γ) / 3 := by
    have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
    unfold qHardP; field_simp; ring
  have hVs : ∀ s, (qLbMDP γ hγ' hγ1).trajectoryExpectedValue
      (qLbMDP γ hγ' hγ1).optimalGreedyPolicy s = qHardValue γ s :=
    fun s ↦ congrFun (qLbMDP_value γ hγ' hγ1) s
  have hout := qLb_output_ae γ η hγ' hγ1 hη0.le hη1.le T
  have hE2 : ∫ d, (qLearningValue (qLbMDP γ hγ' hγ1)
      (qSampledIterate (qLbMDP γ hγ' hγ1) (fun _ ↦ η) T (fun _ _ ↦ 0) d) 2 -
      (qLbMDP γ hγ' hγ1).trajectoryExpectedValue (qLbMDP γ hγ' hγ1).optimalGreedyPolicy 2) ^ 2
        ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T =
      ∫ d, (qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T - 1 / (1 - γ * qHardP γ)) ^ 2
        ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T := by
    apply integral_congr_ae
    filter_upwards [hout] with d hd
    rw [hd.1, hVs 2]
    simp [qHardValue]
  rcases le_or_gt (η * (1 - γ) * T) 4 with hA | hA'
  · ---------------- Case A: small rates, bias at state 2
    refine ⟨2, ?_⟩
    rw [hE2]
    have hmean := qLb_state2_mean γ hγ' hγ1 T η T le_rfl
    have hsq := qLb_sq_integral_le (qLbMDP γ hγ' hγ1) T
      (fun d ↦ qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T) (1 / (1 - γ * qHardP γ))
    have hbias : (∫ d, qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T
        ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T - 1 / (1 - γ * qHardP γ)) ^ 2 =
        ((1 - η * (4 * (1 - γ) / 3)) ^ T * (3 / (4 * (1 - γ)))) ^ 2 := by
      rw [show (∫ d, qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T
        ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T - 1 / (1 - γ * qHardP γ)) ^ 2 =
        (1 / (1 - γ * qHardP γ) - ∫ d, qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T
        ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T) ^ 2 by ring, hmean, hid,
        show (1 : ℝ) / (4 * (1 - γ) / 3) = 3 / (4 * (1 - γ)) by field_simp]
    rw [hbias] at hsq
    exact (qLb_caseA_scalar γ η T hγ hγ1 hη0 hη1 hA hD16 hDpos).trans hsq
  have h4 : 4 ≤ η * (1 - γ) * T := hA'.le
  have hρT := qLb_rho_pow_le γ η T hγ hγ1 hη0.le hη1.le h4
  rcases le_or_gt 1 (η * ((1 - γ) ^ 2 * T)) with hB | hC
  · ---------------- Case B: large rates, variance at state 2
    refine ⟨2, ?_⟩
    rw [hE2]
    have hvar := qLb_variance_le (qLbMDP γ hγ' hγ1) T
      (fun d ↦ qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T) (1 / (1 - γ * qHardP γ))
    refine le_trans ?_ hvar
    exact qLb_caseB_scalar γ η (1 - η * (1 - γ * qHardP γ))
      (η ^ 2 * γ ^ 2 * (qHardP γ * (1 - qHardP γ))) (1 / (1 - γ * qHardP γ)) T hγ hγ1 hη0 hη1
      (by rw [hid]) (by rw [show η ^ 2 * γ ^ 2 * (qHardP γ * (1 - qHardP γ)) =
        η ^ 2 * (γ ^ 2 * (qHardP γ * (1 - qHardP γ))) by ring, hpv]) hVh hB hρT hT1 hD1
      (fun t ↦ ∫ d, (qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) t -
        ∫ e, qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T e) t
          ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T) ^ 2 ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T)
      (fun t ↦ ∫ e, qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T e) t
          ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T)
      (fun t ↦ integral_nonneg (fun d ↦ sq_nonneg _))
      (fun t ht ↦ qLb_state2_var_step γ hγ' hγ1 T η t ht)
      (fun t ht ↦ qLb_state2_mean γ hγ' hγ1 T η t ht)
  · ---------------- Case C: moderate rates, over-estimation at state 1
    have hηs : η ≤ 1 := hη1.le
    have hrow := qLbMDP_rowSpec γ hγ' hγ1
    set b := 5 / 1536 * min (Real.sqrt (η / (1 - γ))) 1 with hb
    have hb0 : 0 ≤ b := by
      rw [hb]; apply mul_nonneg (by norm_num)
      exact le_min (Real.sqrt_nonneg _) zero_le_one
    obtain ⟨hρ0, hρ23, hρ1, hηρ⟩ := qLb_rho_bounds γ η hγ hγ1 hη0 hη1
    rw [← hid] at hρ0 hρ23 hρ1 hηρ
    set τ₀ := (T + 1) / 2 with hτ₀
    have hτT : τ₀ ≤ T := by omega
    have hm : ∀ t, τ₀ ≤ t → t ≤ T →
        b ≤ ∫ d, qLbXiMax γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) t
          ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T := by
      intro t ht1 ht2
      have hdec : (1 - η) ^ (2 * t) ≤ 1 / 3 := by
        have a1 : (1 - η) ^ (2 * t) ≤ (1 - η) ^ T :=
          pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
        have a2 : (1 - η) ^ T ≤ (1 - η * (1 - γ * qHardP γ)) ^ T :=
          pow_le_pow_left₀ (by linarith) hηρ T
        linarith
      exact qLb_xiMax_lower (qLbMDP γ hγ' hγ1) T γ η hγ hγ1 hη0 hηs hrow t ht2 hdec
    have h5 := qLb_step5 (qLbMDP γ hγ' hγ1) T γ η hγ hγ1 hη0 hηs hrow b hb0 τ₀ hτT hm
    have hρhalf : (1 - η * (1 - γ * qHardP γ)) ^ (T - τ₀) ≤ 1 / 2 := by
      exact (qLb_rho_tail _ T τ₀ hρ0 hρ23 hρ1 hρT hT1 (by omega)).2
    have hbl := qLb_b_lower γ η T hγ1 hRT hlog (by linarith)
    have hE1 : ∫ d, qLbAuxValue γ η (qSamplesExtend (qLbMDP γ hγ' hγ1) T d) T
        ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T - (1 - η * (1 - γ)) ^ T / (1 - γ) ≤
        ∫ d, qLearningValue (qLbMDP γ hγ' hγ1)
          (qSampledIterate (qLbMDP γ hγ' hγ1) (fun _ ↦ η) T (fun _ _ ↦ 0) d) 1
          ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T := by
      have := integral_mono_ae (qSampling_integrable (qLbMDP γ hγ' hγ1) T _)
        (qSampling_integrable (qLbMDP γ hγ' hγ1) T _)
        (by filter_upwards [hout] with d hd; exact hd.2.2)
      rw [integral_sub (qSampling_integrable _ T _) (integrable_const _)] at this
      simpa [integral_const] using this
    have hE3 : ∫ d, qLearningValue (qLbMDP γ hγ' hγ1)
          (qSampledIterate (qLbMDP γ hγ' hγ1) (fun _ ↦ η) T (fun _ _ ↦ 0) d) 3
          ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T = (1 - (1 - η * (1 - γ)) ^ T) / (1 - γ) := by
      have : ∫ d, qLearningValue (qLbMDP γ hγ' hγ1)
          (qSampledIterate (qLbMDP γ hγ' hγ1) (fun _ ↦ η) T (fun _ _ ↦ 0) d) 3
          ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T =
          ∫ _d, (1 - (1 - η * (1 - γ)) ^ T) / (1 - γ) ∂qSamplingLaw (qLbMDP γ hγ' hγ1) T :=
        integral_congr_ae (by filter_upwards [hout] with d hd; exact hd.2.1)
      rw [this]; simp
    rcases qLb_caseC_scalar γ b _ (1 / (1 - γ * qHardP γ)) _ _ _ _ _ T hγ hγ1 hb0 hρhalf
      hid h5 hE1 hE3 hRT hlog hbl with h | h
    · refine ⟨1, ?_⟩
      have hsq := qLb_sq_integral_le (qLbMDP γ hγ' hγ1) T
        (fun d ↦ qLearningValue (qLbMDP γ hγ' hγ1)
          (qSampledIterate (qLbMDP γ hγ' hγ1) (fun _ ↦ η) T (fun _ _ ↦ 0) d) 1)
        ((qLbMDP γ hγ' hγ1).trajectoryExpectedValue (qLbMDP γ hγ' hγ1).optimalGreedyPolicy 1)
      rw [hVs 1] at hsq ⊢
      simp only [qHardValue, show ¬((1 : Fin 4) = 0) by decide,
        show ¬((1 : Fin 4) = 3) by decide, ↓reduceIte] at hsq ⊢
      exact h.trans hsq
    · refine ⟨3, ?_⟩
      have hsq := qLb_sq_integral_le (qLbMDP γ hγ' hγ1) T
        (fun d ↦ qLearningValue (qLbMDP γ hγ' hγ1)
          (qSampledIterate (qLbMDP γ hγ' hγ1) (fun _ ↦ η) T (fun _ _ ↦ 0) d) 3)
        ((qLbMDP γ hγ' hγ1).trajectoryExpectedValue (qLbMDP γ hγ' hγ1).optimalGreedyPolicy 3)
      rw [hVs 3] at hsq ⊢
      simp only [qHardValue, show ¬((3 : Fin 4) = 0) by decide, ↓reduceIte] at hsq ⊢
      exact h.trans hsq

end StatisticalRL.QLearning

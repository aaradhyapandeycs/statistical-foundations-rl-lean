import Formalization.ModelFree.QLearningLowerBoundPathwise

/-!
# Mean and variance of the state-2 chain

`eq:EV2` (`chapters/generative_model_model_free.tex:3010–3021`):
`V⋆(2) - E v_t = (1-η(1-γp))^t V⋆(2)`; and the martingale variance recursion behind
`eq:Var-VT-2-LB-769` (lines 3184–3195):
`E(v_{t+1} - E v_{t+1})² ≥ ρ² E(v_t - E v_t)² + η²γ²p(1-p)(E v_t)²`, `ρ = 1-η(1-γp)`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

/-- Agreement of the state-2 (source action) draws at times `1,…,n`. -/
def qLbAgree2 (s s' : ℕ → Fin 4 → Bool → Fin 4) (n : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ n → s k 2 false = s' k 2 false

theorem qLbChain2_congr (γ η : ℝ) (s s' : ℕ → Fin 4 → Bool → Fin 4) (n : ℕ)
    (h : qLbAgree2 s s' n) (t : ℕ) (ht : t ≤ n) :
    qLbChain2 γ η s t = qLbChain2 γ η s' t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [qLbChain2, qLbStay, ih (by omega), h (t + 1) (by omega) ht]

section
variable (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) (N : ℕ)

theorem qLb_integral_mul_state2 (n : ℕ) (F : QSamples (Fin 4) Bool N → ℝ)
    (hF : ∀ d d', qLbAgree2 (qSamplesExtend (qLbMDP γ hγ hγ1) N d)
      (qSamplesExtend (qLbMDP γ hγ hγ1) N d') n → F d = F d')
    (g : Fin 4 → ℝ) :
    ∫ d, F d * g (qSamplesExtend (qLbMDP γ hγ hγ1) N d (n + 1) 2 false)
        ∂qSamplingLaw (qLbMDP γ hγ hγ1) N =
      (∫ d, F d ∂qSamplingLaw (qLbMDP γ hγ hγ1) N) *
        ∫ d, g (qSamplesExtend (qLbMDP γ hγ hγ1) N d (n + 1) 2 false)
          ∂qSamplingLaw (qLbMDP γ hγ hγ1) N := by
  apply qLb_integral_mul_past_layer (qLbMDP γ hγ hγ1) N n F
  · intro d d' h
    exact hF d d' (fun k _ hk ↦ qSamplesExtend_agree_past _ N n d d' h k hk 2 false)
  · intro d d' h
    rw [qSamplesExtend_agree_layer _ N n d d' h]

theorem qLb_integral_state2 (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (g : Fin 4 → ℝ) :
    ∫ d, g (qSamplesExtend (qLbMDP γ hγ hγ1) N d k 2 false) ∂qSamplingLaw (qLbMDP γ hγ hγ1) N =
      qHardP γ * g 2 + (1 - qHardP γ) * g 0 := by
  simp_rw [qSamplesExtend_coord _ N k hk1 hkN]
  rw [qLb_integral_coord]
  simp [Fin.sum_univ_four, qLbMDP, qLbRow, qHardRow]
  ring

/-- Indicator of a stay at state 2. -/
def qLbInd2 (x : Fin 4) : ℝ := if x = 2 then 1 else 0

variable (η : ℝ)

/-- `eq:EV2`: `V⋆(2) - E v_t = ρ^t V⋆(2)` for `t ≤ N`. -/
theorem qLb_state2_mean (t : ℕ) (ht : t ≤ N) :
    1 / (1 - γ * qHardP γ) -
        ∫ d, qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N d) t
          ∂qSamplingLaw (qLbMDP γ hγ hγ1) N =
      (1 - η * (1 - γ * qHardP γ)) ^ t * (1 / (1 - γ * qHardP γ)) := by
  have hden : 1 - γ * qHardP γ ≠ 0 := by
    rw [show 1 - γ * qHardP γ = 4 * (1 - γ) / 3 by
      have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
      unfold qHardP; field_simp; ring]
    intro h; linarith
  induction t with
  | zero => simp [qLbChain2]
  | succ t ih =>
    have ih' := ih (by omega)
    have hpt : ∀ d : QSamples (Fin 4) Bool N,
        qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N d) (t + 1) =
          (1 - η) * qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N d) t + η +
            (η * γ) * (qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N d) t *
              qLbInd2 (qSamplesExtend (qLbMDP γ hγ hγ1) N d (t + 1) 2 false)) := by
      intro d; simp only [qLbChain2, qLbStay, qLbInd2]; ring
    simp_rw [hpt]
    rw [integral_add (qSampling_integrable _ N _) (qSampling_integrable _ N _),
      integral_add (qSampling_integrable _ N _) (integrable_const _), integral_const_mul,
      integral_const_mul,
      qLb_integral_mul_state2 γ hγ hγ1 N t _
        (fun d d' h ↦ qLbChain2_congr γ η _ _ t h t le_rfl) qLbInd2,
      qLb_integral_state2 γ hγ hγ1 N (t + 1) (by omega) ht qLbInd2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, qLbInd2]
    simp only [if_pos rfl, show ¬((0 : Fin 4) = 2) by decide, ↓reduceIte]
    rw [pow_succ]
    set m := ∫ d, qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N d) t
      ∂qSamplingLaw (qLbMDP γ hγ hγ1) N
    have e : 1 / (1 - γ * qHardP γ) - m = (1 - η * (1 - γ * qHardP γ)) ^ t *
        (1 / (1 - γ * qHardP γ)) := ih'
    field_simp at e ⊢
    linear_combination (1 - η * (1 - γ * qHardP γ)) * e

/-- Variance recursion for the state-2 chain. -/
theorem qLb_state2_var_step (t : ℕ) (ht : t + 1 ≤ N) :
    (1 - η * (1 - γ * qHardP γ)) ^ 2 *
        ∫ d, (qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N d) t -
          ∫ e, qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N e) t
            ∂qSamplingLaw (qLbMDP γ hγ hγ1) N) ^ 2 ∂qSamplingLaw (qLbMDP γ hγ hγ1) N +
      η ^ 2 * γ ^ 2 * (qHardP γ * (1 - qHardP γ)) *
        (∫ e, qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N e) t
          ∂qSamplingLaw (qLbMDP γ hγ hγ1) N) ^ 2 ≤
      ∫ d, (qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N d) (t + 1) -
          ∫ e, qLbChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) N e) (t + 1)
            ∂qSamplingLaw (qLbMDP γ hγ hγ1) N) ^ 2 ∂qSamplingLaw (qLbMDP γ hγ hγ1) N := by
  have hp := qHardP_bounds γ hγ hγ1
  set M := qLbMDP γ hγ hγ1
  set ρ := 1 - η * (1 - γ * qHardP γ)
  set p := qHardP γ
  set m := ∫ e, qLbChain2 γ η (qSamplesExtend M N e) t ∂qSamplingLaw M N
  -- mean recursion
  have hm1 : ∫ e, qLbChain2 γ η (qSamplesExtend M N e) (t + 1) ∂qSamplingLaw M N = ρ * m + η := by
    have hpt : ∀ d : QSamples (Fin 4) Bool N,
        qLbChain2 γ η (qSamplesExtend M N d) (t + 1) =
          (1 - η) * qLbChain2 γ η (qSamplesExtend M N d) t + η +
            (η * γ) * (qLbChain2 γ η (qSamplesExtend M N d) t *
              qLbInd2 (qSamplesExtend M N d (t + 1) 2 false)) := by
      intro d; simp only [qLbChain2, qLbStay, qLbInd2]; ring
    simp_rw [hpt]
    rw [integral_add (qSampling_integrable _ N _) (qSampling_integrable _ N _),
      integral_add (qSampling_integrable _ N _) (integrable_const _), integral_const_mul,
      integral_const_mul,
      qLb_integral_mul_state2 γ hγ hγ1 N t _
        (fun d d' h ↦ qLbChain2_congr γ η _ _ t h t le_rfl) qLbInd2,
      qLb_integral_state2 γ hγ hγ1 N (t + 1) (by omega) ht qLbInd2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, qLbInd2]
    simp only [if_pos rfl, show ¬((0 : Fin 4) = 2) by decide, ↓reduceIte]
    simp only [ρ, m, p]; ring
  rw [hm1]
  have hpt : ∀ d : QSamples (Fin 4) Bool N,
      (qLbChain2 γ η (qSamplesExtend M N d) (t + 1) - (ρ * m + η)) ^ 2 =
        ρ ^ 2 * (qLbChain2 γ η (qSamplesExtend M N d) t - m) ^ 2 +
        (2 * ρ * η * γ) * (((qLbChain2 γ η (qSamplesExtend M N d) t - m) *
          qLbChain2 γ η (qSamplesExtend M N d) t) *
            (qLbInd2 (qSamplesExtend M N d (t + 1) 2 false) - p)) +
        (η ^ 2 * γ ^ 2) * (qLbChain2 γ η (qSamplesExtend M N d) t ^ 2 *
            (qLbInd2 (qSamplesExtend M N d (t + 1) 2 false) - p) ^ 2) := by
    intro d; simp only [qLbChain2, qLbStay, qLbInd2, ρ]; ring
  simp_rw [hpt]
  rw [integral_add (qSampling_integrable _ N _) (qSampling_integrable _ N _),
    integral_add (qSampling_integrable _ N _) (qSampling_integrable _ N _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    qLb_integral_mul_state2 γ hγ hγ1 N t
      (fun d ↦ (qLbChain2 γ η (qSamplesExtend M N d) t - m) * qLbChain2 γ η (qSamplesExtend M N d) t)
      (fun d d' h ↦ by
        have hc := qLbChain2_congr γ η _ _ t h t le_rfl
        simp only [M] at *
        rw [hc]) (fun x ↦ qLbInd2 x - p),
    qLb_integral_mul_state2 γ hγ hγ1 N t
      (fun d ↦ qLbChain2 γ η (qSamplesExtend M N d) t ^ 2)
      (fun d d' h ↦ by
        have hc := qLbChain2_congr γ η _ _ t h t le_rfl
        simp only [M] at *
        rw [hc])
      (fun x ↦ (qLbInd2 x - p) ^ 2),
    qLb_integral_state2 γ hγ hγ1 N (t + 1) (by omega) ht (fun x ↦ qLbInd2 x - p),
    qLb_integral_state2 γ hγ hγ1 N (t + 1) (by omega) ht (fun x ↦ (qLbInd2 x - p) ^ 2)]
  simp only [qLbInd2, if_pos rfl, show ¬((0 : Fin 4) = 2) by decide, ↓reduceIte]
  have hsq := qLb_sq_integral_le M N (fun d ↦ qLbChain2 γ η (qSamplesExtend M N d) t) 0
  simp only [sub_zero] at hsq
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp.1 (by linarith)
  have e1 : p * (1 - p) ^ 2 + (1 - p) * (0 - p) ^ 2 = p * (1 - p) := by ring
  have e0 : p * (1 - p) + (1 - p) * (0 - p) = 0 := by ring
  rw [e1, e0]
  have := mul_le_mul_of_nonneg_left hsq
    (by positivity : (0 : ℝ) ≤ η ^ 2 * γ ^ 2 * (p * (1 - p)))
  nlinarith

end

end StatisticalRL.QLearning

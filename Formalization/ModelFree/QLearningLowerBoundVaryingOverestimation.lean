import Formalization.ModelFree.QLearningLowerBoundVaryingMoments

/-!
# The over-estimation recursion with a learning-rate schedule

Time-varying form of Step 5.2–5.4 of the proof of `thm:LB-example-Q-generative`
(`chapters/generative_model_model_free.tex:3369–3520`; repaired Step 5.4, `docs/SOURCE-ISSUES.md#C31`
item 4). Pathwise `Q̂_t(a) - V⋆(1) = C_t + ξ_t(a)`, so `V̂_t - V⋆(1) = C_t + ξ_{t,max}`; in expectation
`e_t = E C_t` obeys `e_{t+1} = (1 - (1-γp) η_{t+1}) e_t + η_{t+1} γp E ξ_{t,max}`. If
`E ξ_{t,max} ≥ b ≥ 0` for `1 ≤ t ≤ N`, then by induction
`(1-γp) e_t ≥ γp b (1 - Π_{1-γp}(1,t))` for `1 ≤ t ≤ N`, with `Π_x(1,t) = ∏_{j=2}^t (1 - x η_j)`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

/-- `Q̂_t(a) - V⋆(1) = C_t + ξ_t(a)` pathwise. -/
theorem qLbvAux_decomp (γ : ℝ) (η : ℕ → ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) (a : Bool) :
    qLbvAuxIterate γ η samples t a - 1 / (1 - γ * qHardP γ) =
      qLbvCommon γ η samples t + qLbvXi γ η samples t a := by
  have hVfix : 1 + γ * qHardP γ * (1 / (1 - γ * qHardP γ)) = 1 / (1 - γ * qHardP γ) := by
    have h1 : 1 - γ * qHardP γ ≠ 0 := by
      rw [qLb_one_sub_gamma_p γ hγ]; intro h; linarith
    field_simp; ring
  induction t generalizing a with
  | zero => simp [qLbvAuxIterate, qLbvCommon, qLbvXi]
  | succ t ih =>
    simp only [qLbvAuxIterate, qLbvCommon, qLbvXi, qLbvAuxValue]
    have h := ih a
    linear_combination (1 - η (t + 1)) * h + η (t + 1) * hVfix

/-- `V̂_t - V⋆(1) = C_t + ξ_{t,max}` pathwise. -/
theorem qLbvAuxValue_decomp (γ : ℝ) (η : ℕ → ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) :
    qLbvAuxValue γ η samples t - 1 / (1 - γ * qHardP γ) =
      qLbvCommon γ η samples t + qLbvXiMax γ η samples t := by
  unfold qLbvAuxValue qLbvXiMax
  rw [← max_sub_sub_right, qLbvAux_decomp γ η hγ hγ1, qLbvAux_decomp γ η hγ hγ1,
    max_add_add_left]

section
variable (M : DiscountedMDP (Fin 4) Bool) (N : ℕ) (γ : ℝ) (η : ℕ → ℝ)

/-- Repaired Step 5.4 with a schedule: if `E ξ_{t,max} ≥ b` for `1 ≤ t ≤ N` (and `N ≥ 1`), then
`γp · b · (1 - Π_{1-γp}(1,N)) ≤ (1-γp)·(E V̂_N - V⋆(1))`. -/
theorem qLbv_step5 (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1)
    (hrow : qLbRowSpec M (qHardP γ)) (b : ℝ) (hN : 1 ≤ N)
    (hm : ∀ t, 1 ≤ t → t ≤ N →
      b ≤ ∫ d, qLbvXiMax γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N) :
    γ * qHardP γ * b * (1 - qLbvProd η (1 - γ * qHardP γ) 1 N) ≤
      (1 - γ * qHardP γ) * (∫ d, qLbvAuxValue γ η (qSamplesExtend M N d) N ∂qSamplingLaw M N -
        1 / (1 - γ * qHardP γ)) := by
  have hγ' : (1 : ℝ) / 4 < γ := by linarith
  have hw1 : γ * qHardP γ = (4 * γ - 1) / 3 := by
    have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
    unfold qHardP; field_simp
  have hw0 : 0 ≤ γ * qHardP γ := by rw [hw1]; linarith
  have hk0 : 0 ≤ 1 - γ * qHardP γ := by rw [hw1]; linarith
  have hk1 : 1 - γ * qHardP γ ≤ 1 := by linarith
  set κ := 1 - γ * qHardP γ with hκ
  set w := γ * qHardP γ with hw
  have hκη : ∀ j, 0 ≤ 1 - κ * η j := fun j ↦ by
    have := hη j
    nlinarith
  let e : ℕ → ℝ := fun t ↦ ∫ d, qLbvCommon γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N
  let m : ℕ → ℝ := fun t ↦ ∫ d, qLbvXiMax γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N
  have hd : ∀ t, ∫ d, qLbvAuxValue γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N -
      1 / κ = e t + m t := by
    intro t
    have := integral_congr_ae (μ := qSamplingLaw M N) (Filter.Eventually.of_forall
      (fun d ↦ qLbvAuxValue_decomp γ η hγ' hγ1 (qSamplesExtend M N d) t))
    rw [integral_sub (qSampling_integrable M N _) (integrable_const _),
      integral_add (qSampling_integrable M N _) (qSampling_integrable M N _)] at this
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this
  have he : ∀ t, e (t + 1) = (1 - κ * η (t + 1)) * e t + η (t + 1) * w * m t := by
    intro t
    have h1 : e (t + 1) = (1 - η (t + 1)) * e t + η (t + 1) * w * (e t + m t) := by
      rw [← hd t]
      simp only [e, qLbvCommon]
      rw [integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
        integral_const_mul, integral_const_mul,
        integral_sub (qSampling_integrable M N _) (integrable_const _)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      ring
    rw [h1, hκ]; ring
  have hm0 : ∀ t, t ≤ N → 0 ≤ m t := fun t ht ↦ qLbv_integral_xiMax_nonneg M N γ η hrow t ht
  have he0 : e 0 = 0 := by simp [e, qLbvCommon]
  have hind : ∀ t, 1 ≤ t → t ≤ N → w * b * (1 - qLbvProd η κ 1 t) ≤ κ * e t := by
    intro t ht1
    induction t, ht1 using Nat.le_induction with
    | base =>
      intro _
      rw [qLbvProd_self, sub_self, mul_zero, he 0, he0, mul_zero, zero_add]
      have := hm0 0 (Nat.zero_le N)
      have := (hη 1).1
      have : 0 ≤ η (0 + 1) * w * m 0 := by positivity
      positivity
    | succ t ht ih =>
      intro htN
      have ih' := ih (by omega)
      have hmt := hm t ht (by omega)
      rw [qLbvProd_succ η κ 1 t ht, he t]
      have h1 := mul_le_mul_of_nonneg_left ih' (hκη (t + 1))
      have h2 : κ * η (t + 1) * w * b ≤ κ * η (t + 1) * w * m t :=
        mul_le_mul_of_nonneg_left hmt (by have := (hη (t + 1)).1; positivity)
      nlinarith
  have hfin := hind N hN le_rfl
  rw [hd N]
  have hmN := hm0 N le_rfl
  nlinarith

end

end StatisticalRL.QLearning

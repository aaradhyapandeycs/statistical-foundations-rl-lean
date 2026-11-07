import Formalization.ModelFree.QLearningLowerBoundXi

/-!
# Step 5.2–5.4: the over-estimation recursion

`chapters/generative_model_model_free.tex:3369–3520`. Pathwise,
`Δ_t(a) = Q̂_t(a) - V⋆(1) = C_t + ξ_t(a)` with a common part `C_t` (the convolution
`∑_k η(1-η)^{t-k} γp Δ_{k-1,max}` of `eq:recursion-Delta-t-max-Q-lb`, written recursively), so
`Δ_{t,max} = C_t + ξ_{t,max}`. In expectation, `e_t = E C_t` obeys
`e_{t+1} = ρ e_t + ηγp E ξ_{t,max}`; with `E ξ_{t,max} ≥ 0` always and `≥ b` from `τ₀` on, this
gives `(1-γp)·E Δ_{N,max} ≥ b (1 - ρ^{N-τ₀})` (the repaired form of Step 5.4; see C31(4)).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

/-- The common part `C_t` of `Δ_t(a)`: `C_0 = 0`, `C_{t+1} = (1-η)C_t + ηγp(V̂_t - V⋆(1))`. -/
noncomputable def qLbCommon (γ η : ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (1 - η) * qLbCommon γ η samples t +
      η * γ * qHardP γ * (qLbAuxValue γ η samples t - 1 / (1 - γ * qHardP γ))

theorem qLbXi_succ (γ η : ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) (a : Bool) :
    qLbXi γ η samples (t + 1) a = (1 - η) * qLbXi γ η samples t a +
      η * γ * (qLbStay samples 1 (t + 1) a - qHardP γ) * qLbAuxValue γ η samples t := by
  have h := qLb_sum_Icc_geom_succ (1 - η)
    (fun k ↦ η * γ * (qLbStay samples 1 k a - qHardP γ) * qLbAuxValue γ η samples (k - 1)) t
  have e : ∀ t : ℕ, qLbXi γ η samples t a = ∑ k ∈ Finset.Icc 1 t, (1 - η) ^ (t - k) *
      (η * γ * (qLbStay samples 1 k a - qHardP γ) * qLbAuxValue γ η samples (k - 1)) := by
    intro t
    unfold qLbXi
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [e, e, h, Nat.add_sub_cancel]

/-- `Q̂_t(a) - V⋆(1) = C_t + ξ_t(a)` pathwise. -/
theorem qLbAux_decomp (γ η : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) (a : Bool) :
    qLbAuxIterate γ η samples t a - 1 / (1 - γ * qHardP γ) =
      qLbCommon γ η samples t + qLbXi γ η samples t a := by
  have hVfix : 1 + γ * qHardP γ * (1 / (1 - γ * qHardP γ)) = 1 / (1 - γ * qHardP γ) := by
    have h1 : 1 - γ * qHardP γ ≠ 0 := by
      rw [show 1 - γ * qHardP γ = 4 * (1 - γ) / 3 by
        have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
        unfold qHardP; field_simp; ring]
      intro h; linarith
    field_simp; ring
  induction t generalizing a with
  | zero => simp [qLbAuxIterate, qLbCommon, qLbXi]
  | succ t ih =>
    rw [qLbXi_succ]
    simp only [qLbAuxIterate, qLbCommon, qLbAuxValue]
    have h := ih a
    linear_combination (1 - η) * h + η * hVfix

/-- `Δ_{t,max} = C_t + ξ_{t,max}` pathwise (`eq:recursion-Delta-t-max-Q-lb`). -/
theorem qLbAuxValue_decomp (γ η : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) :
    qLbAuxValue γ η samples t - 1 / (1 - γ * qHardP γ) =
      qLbCommon γ η samples t + qLbXiMax γ η samples t := by
  unfold qLbAuxValue qLbXiMax
  rw [← max_sub_sub_right, qLbAux_decomp γ η hγ hγ1, qLbAux_decomp γ η hγ hγ1, max_add_add_left]

section
variable (M : DiscountedMDP (Fin 4) Bool) (N : ℕ) (γ η : ℝ)

/-- Step 5.4 (repaired): `(1-γp)·(E V̂_N - V⋆(1)) ≥ b(1-ρ^{N-τ₀})` whenever
`E ξ_{t,max} ≥ b ≥ 0` for `τ₀ ≤ t ≤ N`. -/
theorem qLb_step5 (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hrow : qLbRowSpec M (qHardP γ)) (b : ℝ) (hb0 : 0 ≤ b) (τ₀ : ℕ) (hτ : τ₀ ≤ N)
    (hm : ∀ t, τ₀ ≤ t → t ≤ N →
      b ≤ ∫ d, qLbXiMax γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N) :
    b * (1 - (1 - η * (1 - γ * qHardP γ)) ^ (N - τ₀)) ≤
      (1 - γ * qHardP γ) * (∫ d, qLbAuxValue γ η (qSamplesExtend M N d) N ∂qSamplingLaw M N -
        1 / (1 - γ * qHardP γ)) := by
  have hγ' : (1 : ℝ) / 4 < γ := by linarith
  have hp := qHardP_bounds γ hγ' hγ1
  have hw1 : γ * qHardP γ = (4 * γ - 1) / 3 := by
    have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
    unfold qHardP; field_simp
  have hw0 : 0 ≤ γ * qHardP γ := by rw [hw1]; linarith
  have hwl : γ * qHardP γ < 1 := by rw [hw1]; linarith
  have hρ0 : 0 ≤ 1 - η * (1 - γ * qHardP γ) := by nlinarith
  have hρ1 : 1 - η * (1 - γ * qHardP γ) ≤ 1 := by nlinarith
  -- expectations
  let e : ℕ → ℝ := fun t ↦ ∫ d, qLbCommon γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N
  let m : ℕ → ℝ := fun t ↦ ∫ d, qLbXiMax γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N
  have hd : ∀ t, ∫ d, qLbAuxValue γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N -
      1 / (1 - γ * qHardP γ) = e t + m t := by
    intro t
    have := integral_congr_ae (μ := qSamplingLaw M N) (Filter.Eventually.of_forall
      (fun d ↦ qLbAuxValue_decomp γ η hγ' hγ1 (qSamplesExtend M N d) t))
    rw [integral_sub (qSampling_integrable M N _) (integrable_const _),
      integral_add (qSampling_integrable M N _) (qSampling_integrable M N _)] at this
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at this
    exact this
  have he : ∀ t, e (t + 1) = (1 - η * (1 - γ * qHardP γ)) * e t +
      η * (γ * qHardP γ) * m t := by
    intro t
    have h1 : e (t + 1) = (1 - η) * e t + η * (γ * qHardP γ) * (e t + m t) := by
      rw [← hd t]
      simp only [e, qLbCommon]
      rw [integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
        integral_const_mul, integral_const_mul,
        integral_sub (qSampling_integrable M N _) (integrable_const _)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      ring
    rw [h1]; ring
  have hm0 : ∀ t, t ≤ N → 0 ≤ m t := by
    intro t ht
    have := integral_mono (qSampling_integrable M N _) (qSampling_integrable M N _)
      (fun d ↦ le_max_left (qLbXi γ η (qSamplesExtend M N d) t false)
        (qLbXi γ η (qSamplesExtend M N d) t true))
    rw [qLb_integral_xi M N γ η hrow t ht false] at this
    exact this
  have he0 : ∀ t, t ≤ N → 0 ≤ e t := by
    intro t ht
    induction t with
    | zero => simp [e, qLbCommon]
    | succ t ih =>
      rw [he t]
      have := ih (by omega)
      have := hm0 t (by omega)
      have : 0 ≤ η * (γ * qHardP γ) := mul_nonneg hη0.le hw0
      positivity
  have hgrow : ∀ j, τ₀ + j ≤ N → η * (γ * qHardP γ) * b * (1 - (1 - η * (1 - γ * qHardP γ)) ^ j) ≤
      e (τ₀ + j) * (η * (1 - γ * qHardP γ)) := by
    intro j
    induction j with
    | zero =>
      intro h
      simp only [pow_zero, sub_self, mul_zero, add_zero]
      exact mul_nonneg (he0 τ₀ (by omega)) (by nlinarith)
    | succ j ih =>
      intro h
      have ih' := ih (by omega)
      have hmj := hm (τ₀ + j) (by omega) (by omega)
      rw [show τ₀ + (j + 1) = (τ₀ + j) + 1 by ring, he]
      have h1 : η * (γ * qHardP γ) * b ≤ η * (γ * qHardP γ) * m (τ₀ + j) :=
        mul_le_mul_of_nonneg_left hmj (mul_nonneg hη0.le hw0)
      have h2 := mul_le_mul_of_nonneg_left ih' hρ0
      have h3 : 0 ≤ η * (1 - γ * qHardP γ) := by nlinarith
      have h4 := mul_le_mul_of_nonneg_right h1 h3
      rw [pow_succ]
      nlinarith
  have hN := hgrow (N - τ₀) (by omega)
  rw [show τ₀ + (N - τ₀) = N by omega] at hN
  have hN' : (γ * qHardP γ) * b * (1 - (1 - η * (1 - γ * qHardP γ)) ^ (N - τ₀)) ≤
      e N * (1 - γ * qHardP γ) := by
    have : η * ((γ * qHardP γ) * b * (1 - (1 - η * (1 - γ * qHardP γ)) ^ (N - τ₀))) ≤
        η * (e N * (1 - γ * qHardP γ)) := by
      calc _ = η * (γ * qHardP γ) * b * (1 - (1 - η * (1 - γ * qHardP γ)) ^ (N - τ₀)) := by ring
        _ ≤ e N * (η * (1 - γ * qHardP γ)) := hN
        _ = η * (e N * (1 - γ * qHardP γ)) := by ring
    exact le_of_mul_le_mul_left this hη0
  have hmN := hm N hτ le_rfl
  rw [hd N]
  have hr0 : 0 ≤ (1 - η * (1 - γ * qHardP γ)) ^ (N - τ₀) := pow_nonneg hρ0 _
  have hr1 : (1 - η * (1 - γ * qHardP γ)) ^ (N - τ₀) ≤ 1 := pow_le_one₀ hρ0 hρ1
  have h5 : b * (1 - γ * qHardP γ) ≤ m N * (1 - γ * qHardP γ) :=
    mul_le_mul_of_nonneg_right hmN (by linarith)
  have h6 : b * (1 - (1 - η * (1 - γ * qHardP γ)) ^ (N - τ₀)) ≤
      b * (1 - (γ * qHardP γ) * (1 - η * (1 - γ * qHardP γ)) ^ (N - τ₀)) := by
    apply mul_le_mul_of_nonneg_left _ hb0
    nlinarith
  nlinarith

end

end StatisticalRL.QLearning

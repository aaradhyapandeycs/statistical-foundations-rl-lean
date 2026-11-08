import Formalization.ModelFree.QLearningLowerBoundVaryingDefinitions
import Formalization.ModelFree.QLearningLowerBoundRescaledRates
import Formalization.ModelFree.QLearningLowerBoundXi

/-!
# Moments of the time-varying auxiliary sequence; time-varying Lemma 4.15

Case (i) of `thm:LB-example-Q-generative` (`chapters/generative_model_model_free.tex:969–982`) needs
the over-estimation lower bound of `lem:lower-bound-E-xi-lower-Q` (lines 3429–3449) for a learning
rate schedule. With `ζ_t = ξ_t(1) - ξ_t(2)`, which satisfies
`ζ_{t+1} = (1-η_{t+1}) ζ_t + η_{t+1} γ D_{t+1} V̂_t`, the product law gives exact recursions for
`E ζ_t²` and `E ζ_t⁴`; by induction
`γ² 2p(1-p) V⋆² S₂(t) ≤ E ζ_t² ≤ ν S₂(t)` and `E ζ_t⁴ ≤ 3ν² S₂(t)² + ν h² S₄(t)`
(`h = 1/(1-γ)`, `ν = γ² 2p(1-p) h²`, `S₂`, `S₄` from `Rates.lean`) for every schedule with
`0 ≤ η_t ≤ 1`. The moment route of `QLearningLowerBoundXi.lean` (not the printed Freedman route,
`docs/SOURCE-ISSUES.md#C31` item 3) then gives `E ξ_{t,max} ≥ (5/1536) min(√(η̄/(1-γ)), 1)` for any
`η̄ > 0` with `η̄/3 ≤ S₂(t) ≤ η̄` and `S₄(t) ≤ η̄² S₂(t)`; for the rescaled linear schedule with
`c_η(1-γ) ≤ 1` these hold with `η̄ = η_t` for every `1 ≤ t` (weight bounds `(A3)`, `(A4)`).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

/-! ### Pathwise facts -/

theorem qLbvAuxIterate_bounds (γ : ℝ) (η : ℕ → ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1) (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) (a : Bool) :
    0 ≤ qLbvAuxIterate γ η samples t a ∧ qLbvAuxIterate γ η samples t a ≤ 1 / (1 - γ) := by
  have hg : 0 < 1 - γ := by linarith
  set h := 1 / (1 - γ) with hh
  have hh0 : 0 ≤ h := by positivity
  induction t generalizing a with
  | zero =>
    simp only [qLbvAuxIterate]
    rw [qLb_vstar_eq γ hγ hγ1]
    constructor
    · positivity
    · rw [hh, div_le_div_iff₀ (by positivity) hg]; linarith
  | succ t ih =>
    simp only [qLbvAuxIterate]
    obtain ⟨hη0, hη1⟩ := hη (t + 1)
    set V := max (qLbvAuxIterate γ η samples t false) (qLbvAuxIterate γ η samples t true)
    have hV0 : 0 ≤ V := le_max_of_le_left (ih false).1
    have hV1 : V ≤ h := max_le (ih false).2 (ih true).2
    have hX0 := qLbStay_nonneg samples 1 (t + 1) a
    have hX1 := qLbStay_le_one samples 1 (t + 1) a
    set X := qLbStay samples 1 (t + 1) a
    have hXV0 : 0 ≤ X * V := mul_nonneg hX0 hV0
    have hXV1 : X * V ≤ h := by nlinarith
    have hγ0 : 0 ≤ γ := by linarith
    have hγh : 1 + γ * h = h := by rw [hh]; field_simp; ring
    have h1 : γ * (X * V) ≤ γ * h := mul_le_mul_of_nonneg_left hXV1 hγ0
    have h2 : 0 ≤ γ * (X * V) := mul_nonneg hγ0 hXV0
    have hQ := ih a
    have e1 : 0 ≤ 1 - η (t + 1) := by linarith
    constructor
    · have := mul_nonneg e1 hQ.1
      have := mul_nonneg hη0 (by nlinarith : (0 : ℝ) ≤ 1 + γ * X * V)
      nlinarith
    · have a1 := mul_le_mul_of_nonneg_left hQ.2 e1
      have a2 : η (t + 1) * (1 + γ * X * V) ≤ η (t + 1) * h := by
        apply mul_le_mul_of_nonneg_left _ hη0
        have : γ * X * V = γ * (X * V) := by ring
        rw [this]; linarith
      nlinarith

theorem qLbvAuxValue_bounds (γ : ℝ) (η : ℕ → ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1) (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) :
    0 ≤ qLbvAuxValue γ η samples t ∧ qLbvAuxValue γ η samples t ≤ 1 / (1 - γ) :=
  ⟨le_max_of_le_left (qLbvAuxIterate_bounds γ η hγ hγ1 hη samples t false).1,
    max_le (qLbvAuxIterate_bounds γ η hγ hγ1 hη samples t false).2
      (qLbvAuxIterate_bounds γ η hγ hγ1 hη samples t true).2⟩

theorem qLbvAuxIterate_congr (γ : ℝ) (η : ℕ → ℝ) (s s' : ℕ → Fin 4 → Bool → Fin 4) (n : ℕ)
    (h : qLbAgree1 s s' n) (t : ℕ) (ht : t ≤ n) :
    qLbvAuxIterate γ η s t = qLbvAuxIterate γ η s' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext a
    simp only [qLbvAuxIterate, qLbStay, ih (by omega), h (t + 1) (by omega) ht a]

theorem qLbvAuxValue_congr (γ : ℝ) (η : ℕ → ℝ) (s s' : ℕ → Fin 4 → Bool → Fin 4) (n : ℕ)
    (h : qLbAgree1 s s' n) (t : ℕ) (ht : t ≤ n) :
    qLbvAuxValue γ η s t = qLbvAuxValue γ η s' t := by
  simp only [qLbvAuxValue, qLbvAuxIterate_congr γ η s s' n h t ht]

theorem qLbvXi_congr (γ : ℝ) (η : ℕ → ℝ) (s s' : ℕ → Fin 4 → Bool → Fin 4) (n : ℕ)
    (h : qLbAgree1 s s' n) (t : ℕ) (ht : t ≤ n) :
    qLbvXi γ η s t = qLbvXi γ η s' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext a
    simp only [qLbvXi, qLbStay, ih (by omega), h (t + 1) (by omega) ht a,
      qLbvAuxValue_congr γ η s s' n h t (by omega)]

/-- `ζ_{t+1} = (1-η_{t+1}) ζ_t + η_{t+1} γ V̂_t D_{t+1}` with `ζ = ξ(1) - ξ(2)`. -/
theorem qLbvXi_sub_succ (γ : ℝ) (η : ℕ → ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) :
    qLbvXi γ η samples (t + 1) false - qLbvXi γ η samples (t + 1) true =
      (1 - η (t + 1)) * (qLbvXi γ η samples t false - qLbvXi γ η samples t true) +
        (η (t + 1) * γ) * qLbvAuxValue γ η samples t *
          qLbD (samples (t + 1) 1 false) (samples (t + 1) 1 true) := by
  simp only [qLbvXi, qLbD, qLbInd, qLbStay]
  ring

/-! ### Moments under the product law -/

section Moments
variable (M : DiscountedMDP (Fin 4) Bool) (N : ℕ) (γ : ℝ) (η : ℕ → ℝ)

/-- `E[V̂_t] ≥ V⋆(1)` for `t ≤ N` (via `E Q̂_t(1) ≥ V⋆(1)`). -/
theorem qLbv_auxIterate_integral_ge (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1) (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) :
    1 / (1 - γ * qHardP γ) ≤
      ∫ d, qLbvAuxIterate γ η (qSamplesExtend M N d) t false ∂qSamplingLaw M N := by
  have hp := qHardP_bounds γ hγ hγ1
  induction t with
  | zero => simp [qLbvAuxIterate]
  | succ t ih =>
    have ih' := ih (by omega)
    obtain ⟨hη0, hη1⟩ := hη (t + 1)
    have hV : ∫ d, qLbvAuxIterate γ η (qSamplesExtend M N d) t false ∂qSamplingLaw M N ≤
        ∫ d, qLbvAuxValue γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N :=
      integral_mono (qSampling_integrable M N _) (qSampling_integrable M N _)
        (fun d ↦ le_max_left _ _)
    have hpt : ∀ d : QSamples (Fin 4) Bool N,
        qLbvAuxIterate γ η (qSamplesExtend M N d) (t + 1) false =
          (1 - η (t + 1)) * qLbvAuxIterate γ η (qSamplesExtend M N d) t false +
            η (t + 1) * (1 + γ * qHardP γ * qLbvAuxValue γ η (qSamplesExtend M N d) t) +
          (η (t + 1) * γ) * (qLbvAuxValue γ η (qSamplesExtend M N d) t *
            (qLbStay (qSamplesExtend M N d) 1 (t + 1) false - qHardP γ)) := by
      intro d; simp only [qLbvAuxIterate, qLbvAuxValue]; ring
    have hcent := qLb_integral_mul_centered M N γ hrow t ht
      (fun d ↦ qLbvAuxValue γ η (qSamplesExtend M N d) t)
      (fun d d' h ↦ qLbvAuxValue_congr γ η _ _ t h t le_rfl) false
    simp_rw [hpt]
    rw [integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
      integral_const_mul, hcent, integral_add (qSampling_integrable M N _)
        (qSampling_integrable M N _), integral_const_mul, integral_const_mul,
      integral_add (integrable_const _) (qSampling_integrable M N _), integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
    have hVfix : 1 + γ * qHardP γ * (1 / (1 - γ * qHardP γ)) = 1 / (1 - γ * qHardP γ) := by
      have h1 : 1 - γ * qHardP γ ≠ 0 := by
        rw [qLb_one_sub_gamma_p γ hγ]; intro h; linarith
      field_simp; ring
    have hη' : 0 ≤ 1 - η (t + 1) := by linarith
    have hγp : 0 ≤ γ * qHardP γ := mul_nonneg (by linarith) hp.1
    nlinarith [mul_le_mul_of_nonneg_left ih' hη', mul_nonneg hη0 hγp,
      mul_le_mul_of_nonneg_left (ih'.trans hV) (mul_nonneg hη0 hγp)]

theorem qLbv_auxValue_integral_ge (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1) (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) :
    1 / (1 - γ * qHardP γ) ≤ ∫ d, qLbvAuxValue γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N :=
  (qLbv_auxIterate_integral_ge M N γ η hγ hγ1 hη hrow t ht).trans
    (integral_mono (qSampling_integrable M N _) (qSampling_integrable M N _)
      (fun _ ↦ le_max_left _ _))

/-- `E[ξ_t(a)] = 0` for `t ≤ N`. -/
theorem qLbv_integral_xi (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) (a : Bool) :
    ∫ d, qLbvXi γ η (qSamplesExtend M N d) t a ∂qSamplingLaw M N = 0 := by
  induction t with
  | zero => simp [qLbvXi]
  | succ t ih =>
    have hpt : ∀ d : QSamples (Fin 4) Bool N,
        qLbvXi γ η (qSamplesExtend M N d) (t + 1) a =
          (1 - η (t + 1)) * qLbvXi γ η (qSamplesExtend M N d) t a +
          (η (t + 1) * γ) * (qLbvAuxValue γ η (qSamplesExtend M N d) t *
            (qLbStay (qSamplesExtend M N d) 1 (t + 1) a - qHardP γ)) := by
      intro d; simp only [qLbvXi]; ring
    simp_rw [hpt]
    rw [integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
      integral_const_mul, integral_const_mul, ih (by omega),
      qLb_integral_mul_centered M N γ hrow t ht
        (fun d ↦ qLbvAuxValue γ η (qSamplesExtend M N d) t)
        (fun d d' h ↦ qLbvAuxValue_congr γ η _ _ t h t le_rfl) a]
    ring

/-- `E[ξ_{t,max}] = E|ξ_t(1) - ξ_t(2)|/2`. -/
theorem qLbv_integral_xiMax (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) :
    ∫ d, qLbvXiMax γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N =
      (∫ d, |qLbvXi γ η (qSamplesExtend M N d) t false -
        qLbvXi γ η (qSamplesExtend M N d) t true| ∂qSamplingLaw M N) / 2 := by
  unfold qLbvXiMax
  simp_rw [qLb_max_eq]
  rw [integral_div, integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    qLbv_integral_xi M N γ η hrow t ht false, qLbv_integral_xi M N γ η hrow t ht true]
  ring

/-- `E ξ_{t,max} ≥ 0` for `t ≤ N`. -/
theorem qLbv_integral_xiMax_nonneg (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) :
    0 ≤ ∫ d, qLbvXiMax γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N := by
  have := integral_mono (qSampling_integrable M N _) (qSampling_integrable M N _)
    (fun d ↦ le_max_left (qLbvXi γ η (qSamplesExtend M N d) t false)
      (qLbvXi γ η (qSamplesExtend M N d) t true))
  rw [qLbv_integral_xi M N γ η hrow t ht false] at this
  exact this

/-- Exact second-moment recursion for `ζ`. -/
theorem qLbv_zeta_sq_succ (hrow : qLbRowSpec M (qHardP γ)) (n : ℕ) (hn : n + 1 ≤ N) :
    ∫ d, (qLbvXi γ η (qSamplesExtend M N d) (n + 1) false -
        qLbvXi γ η (qSamplesExtend M N d) (n + 1) true) ^ 2 ∂qSamplingLaw M N =
      (1 - η (n + 1)) ^ 2 * ∫ d, (qLbvXi γ η (qSamplesExtend M N d) n false -
        qLbvXi γ η (qSamplesExtend M N d) n true) ^ 2 ∂qSamplingLaw M N +
        (η (n + 1) * γ) ^ 2 * (2 * (qHardP γ * (1 - qHardP γ))) *
          ∫ d, qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N := by
  set a := 1 - η (n + 1)
  set c := η (n + 1) * γ
  have hpt : ∀ d : QSamples (Fin 4) Bool N,
      (qLbvXi γ η (qSamplesExtend M N d) (n + 1) false -
        qLbvXi γ η (qSamplesExtend M N d) (n + 1) true) ^ 2 =
        a ^ 2 * (qLbvXi γ η (qSamplesExtend M N d) n false -
          qLbvXi γ η (qSamplesExtend M N d) n true) ^ 2 +
        (2 * a * c) * (((qLbvXi γ η (qSamplesExtend M N d) n false -
          qLbvXi γ η (qSamplesExtend M N d) n true) *
          qLbvAuxValue γ η (qSamplesExtend M N d) n) *
            qLbD (qSamplesExtend M N d (n + 1) 1 false)
              (qSamplesExtend M N d (n + 1) 1 true) ^ 1) +
        c ^ 2 * (qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 2 *
            qLbD (qSamplesExtend M N d (n + 1) 1 false)
              (qSamplesExtend M N d (n + 1) 1 true) ^ 2) := by
    intro d; rw [qLbvXi_sub_succ]; ring
  simp_rw [hpt]
  rw [integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    qLb_integral_mul_Dpow M N n _ (fun d d' h ↦ by
      simp only [qLbvXi_congr γ η _ _ n h n le_rfl, qLbvAuxValue_congr γ η _ _ n h n le_rfl]) 1,
    qLb_integral_mul_Dpow M N n _ (fun d d' h ↦ by
      simp only [qLbvAuxValue_congr γ η _ _ n h n le_rfl]) 2]
  simp_rw [pow_one]
  rw [qLb_integral_D M N γ hrow (n + 1) (by omega) hn,
    qLb_integral_D_sq M N γ hrow (n + 1) (by omega) hn]
  ring

/-- Exact fourth-moment recursion for `ζ` (odd moments of `D` vanish, `D³ = D`, `D⁴ = D²`). -/
theorem qLbv_zeta_four_succ (hrow : qLbRowSpec M (qHardP γ)) (n : ℕ) (hn : n + 1 ≤ N) :
    ∫ d, (qLbvXi γ η (qSamplesExtend M N d) (n + 1) false -
        qLbvXi γ η (qSamplesExtend M N d) (n + 1) true) ^ 4 ∂qSamplingLaw M N =
      (1 - η (n + 1)) ^ 4 * ∫ d, (qLbvXi γ η (qSamplesExtend M N d) n false -
        qLbvXi γ η (qSamplesExtend M N d) n true) ^ 4 ∂qSamplingLaw M N +
        6 * (1 - η (n + 1)) ^ 2 * (η (n + 1) * γ) ^ 2 * (2 * (qHardP γ * (1 - qHardP γ))) *
          ∫ d, (qLbvXi γ η (qSamplesExtend M N d) n false -
            qLbvXi γ η (qSamplesExtend M N d) n true) ^ 2 *
            qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N +
        (η (n + 1) * γ) ^ 4 * (2 * (qHardP γ * (1 - qHardP γ))) *
          ∫ d, qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 4 ∂qSamplingLaw M N := by
  set a := 1 - η (n + 1)
  set c := η (n + 1) * γ
  have hpt : ∀ d : QSamples (Fin 4) Bool N,
      (qLbvXi γ η (qSamplesExtend M N d) (n + 1) false -
        qLbvXi γ η (qSamplesExtend M N d) (n + 1) true) ^ 4 =
        a ^ 4 * (qLbvXi γ η (qSamplesExtend M N d) n false -
          qLbvXi γ η (qSamplesExtend M N d) n true) ^ 4 +
        (4 * a ^ 3 * c) * (((qLbvXi γ η (qSamplesExtend M N d) n false -
          qLbvXi γ η (qSamplesExtend M N d) n true) ^ 3 *
          qLbvAuxValue γ η (qSamplesExtend M N d) n) *
            qLbD (qSamplesExtend M N d (n + 1) 1 false)
              (qSamplesExtend M N d (n + 1) 1 true) ^ 1) +
        (6 * a ^ 2 * c ^ 2) * (((qLbvXi γ η (qSamplesExtend M N d) n false -
          qLbvXi γ η (qSamplesExtend M N d) n true) ^ 2 *
          qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 2) *
            qLbD (qSamplesExtend M N d (n + 1) 1 false)
              (qSamplesExtend M N d (n + 1) 1 true) ^ 2) +
        (4 * a * c ^ 3) * (((qLbvXi γ η (qSamplesExtend M N d) n false -
          qLbvXi γ η (qSamplesExtend M N d) n true) *
          qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 3) *
            qLbD (qSamplesExtend M N d (n + 1) 1 false)
              (qSamplesExtend M N d (n + 1) 1 true) ^ 1) +
        c ^ 4 * (qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 4 *
            qLbD (qSamplesExtend M N d (n + 1) 1 false)
              (qSamplesExtend M N d (n + 1) 1 true) ^ 2) := by
    intro d
    rw [qLbvXi_sub_succ]
    have h3 := qLbD_cube (qSamplesExtend M N d (n + 1) 1 false)
      (qSamplesExtend M N d (n + 1) 1 true)
    have h4 := qLbD_four (qSamplesExtend M N d (n + 1) 1 false)
      (qSamplesExtend M N d (n + 1) 1 true)
    set D := qLbD (qSamplesExtend M N d (n + 1) 1 false) (qSamplesExtend M N d (n + 1) 1 true)
    set S := qLbvXi γ η (qSamplesExtend M N d) n false - qLbvXi γ η (qSamplesExtend M N d) n true
    set V := qLbvAuxValue γ η (qSamplesExtend M N d) n
    have e : (a * S + c * V * D) ^ 4 = a ^ 4 * S ^ 4 + 4 * a ^ 3 * c * S ^ 3 * V * D +
        6 * a ^ 2 * c ^ 2 * S ^ 2 * V ^ 2 * D ^ 2 + 4 * a * c ^ 3 * S * V ^ 3 * D ^ 3 +
        c ^ 4 * V ^ 4 * D ^ 4 := by ring
    rw [e, h3, h4]
    ring
  have hS : ∀ d d' : QSamples (Fin 4) Bool N,
      qLbAgree1 (qSamplesExtend M N d) (qSamplesExtend M N d') n →
      qLbvXi γ η (qSamplesExtend M N d) n = qLbvXi γ η (qSamplesExtend M N d') n :=
    fun d d' h ↦ qLbvXi_congr γ η _ _ n h n le_rfl
  have hV : ∀ d d' : QSamples (Fin 4) Bool N,
      qLbAgree1 (qSamplesExtend M N d) (qSamplesExtend M N d') n →
      qLbvAuxValue γ η (qSamplesExtend M N d) n = qLbvAuxValue γ η (qSamplesExtend M N d') n :=
    fun d d' h ↦ qLbvAuxValue_congr γ η _ _ n h n le_rfl
  simp_rw [hpt]
  rw [integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul,
    qLb_integral_mul_Dpow M N n
      (fun d ↦ (qLbvXi γ η (qSamplesExtend M N d) n false -
          qLbvXi γ η (qSamplesExtend M N d) n true) ^ 3 *
        qLbvAuxValue γ η (qSamplesExtend M N d) n)
      (fun d d' h ↦ by simp only [hS d d' h, hV d d' h]) 1,
    qLb_integral_mul_Dpow M N n
      (fun d ↦ (qLbvXi γ η (qSamplesExtend M N d) n false -
          qLbvXi γ η (qSamplesExtend M N d) n true) ^ 2 *
        qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 2)
      (fun d d' h ↦ by simp only [hS d d' h, hV d d' h]) 2,
    qLb_integral_mul_Dpow M N n
      (fun d ↦ (qLbvXi γ η (qSamplesExtend M N d) n false -
          qLbvXi γ η (qSamplesExtend M N d) n true) *
        qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 3)
      (fun d d' h ↦ by simp only [hS d d' h, hV d d' h]) 1,
    qLb_integral_mul_Dpow M N n
      (fun d ↦ qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 4)
      (fun d d' h ↦ by simp only [hV d d' h]) 2]
  simp_rw [pow_one]
  rw [qLb_integral_D M N γ hrow (n + 1) (by omega) hn,
    qLb_integral_D_sq M N γ hrow (n + 1) (by omega) hn]
  ring

end Moments

/-- Scalar step of the time-varying fourth-moment induction. -/
theorem qLbv_scalar_step4 (m4 m4' X Y ν h A B a e : ℝ)
    (e4 : m4' = a ^ 4 * m4 + X + Y) (ih4 : m4 ≤ 3 * ν ^ 2 * A ^ 2 + ν * h ^ 2 * B)
    (t1 : X ≤ 6 * a ^ 2 * e ^ 2 * ν * (ν * A)) (t2 : Y ≤ ν * h ^ 2 * e ^ 4) :
    m4' ≤ 3 * ν ^ 2 * (a ^ 2 * A + e ^ 2) ^ 2 + ν * h ^ 2 * (a ^ 4 * B + e ^ 4) := by
  have h1 : a ^ 4 * m4 ≤ a ^ 4 * (3 * ν ^ 2 * A ^ 2 + ν * h ^ 2 * B) :=
    mul_le_mul_of_nonneg_left ih4 (by positivity)
  have h2 : 0 ≤ 3 * ν ^ 2 * e ^ 4 := by positivity
  have e : 3 * ν ^ 2 * (a ^ 2 * A + e ^ 2) ^ 2 + ν * h ^ 2 * (a ^ 4 * B + e ^ 4) =
      a ^ 4 * (3 * ν ^ 2 * A ^ 2 + ν * h ^ 2 * B) + 6 * a ^ 2 * e ^ 2 * ν * (ν * A) +
        ν * h ^ 2 * e ^ 4 + 3 * ν ^ 2 * e ^ 4 := by ring
  linarith

section Moments2
variable (M : DiscountedMDP (Fin 4) Bool) (N : ℕ) (γ : ℝ) (η : ℕ → ℝ)

/-- Second- and fourth-moment bounds for `ζ_t`, by induction on `t ≤ N`, for any schedule with
`0 ≤ η_t ≤ 1`. -/
theorem qLbv_zeta_moment_bounds (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1)
    (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) :
    let q2 := 2 * (qHardP γ * (1 - qHardP γ))
    let h := 1 / (1 - γ)
    let ν := γ ^ 2 * q2 * h ^ 2
    γ ^ 2 * q2 * (1 / (1 - γ * qHardP γ)) ^ 2 * qLbvSq2 η t ≤
        ∫ d, (qLbvXi γ η (qSamplesExtend M N d) t false -
          qLbvXi γ η (qSamplesExtend M N d) t true) ^ 2 ∂qSamplingLaw M N ∧
      ∫ d, (qLbvXi γ η (qSamplesExtend M N d) t false -
          qLbvXi γ η (qSamplesExtend M N d) t true) ^ 2 ∂qSamplingLaw M N ≤ ν * qLbvSq2 η t ∧
      ∫ d, (qLbvXi γ η (qSamplesExtend M N d) t false -
          qLbvXi γ η (qSamplesExtend M N d) t true) ^ 4 ∂qSamplingLaw M N ≤
        3 * ν ^ 2 * qLbvSq2 η t ^ 2 + ν * h ^ 2 * qLbvSq4 η t := by
  intro q2 h ν
  have hγ' : (1 : ℝ) / 4 < γ := by linarith
  have hp := qHardP_bounds γ hγ' hγ1
  have hq2 : 0 ≤ q2 := by
    have := mul_nonneg hp.1 (by linarith : (0 : ℝ) ≤ 1 - qHardP γ); positivity
  have hh0 : 0 ≤ h := by
    have : 0 < 1 - γ := by linarith
    positivity
  have hν0 : 0 ≤ ν := by positivity
  have hVh0 : 0 ≤ 1 / (1 - γ * qHardP γ) := by
    rw [qLb_vstar_eq γ hγ' hγ1]
    have : 0 < 1 - γ := by linarith
    positivity
  induction t with
  | zero => simp [qLbvXi, qLbvSq2, qLbvSq4]
  | succ n ih =>
    obtain ⟨ih1, ih2, ih4⟩ := ih (by omega)
    obtain ⟨he0, he1⟩ := hη (n + 1)
    set e := η (n + 1) with he
    have ha0 : 0 ≤ 1 - e := by linarith
    have hS2 : qLbvSq2 η (n + 1) = (1 - e) ^ 2 * qLbvSq2 η n + e ^ 2 := rfl
    have hS4 : qLbvSq4 η (n + 1) = (1 - e) ^ 4 * qLbvSq4 η n + e ^ 4 := rfl
    set A := qLbvSq2 η n
    set B := qLbvSq4 η n
    have hA0 : 0 ≤ A := qLbvSq2_nonneg η n
    have hVb := fun d : QSamples (Fin 4) Bool N ↦
      qLbvAuxValue_bounds γ η hγ' hγ1 hη (qSamplesExtend M N d) n
    have hV2up : ∫ d, qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N ≤ h ^ 2 := by
      calc _ ≤ ∫ _d, h ^ 2 ∂qSamplingLaw M N :=
            integral_mono (qSampling_integrable M N _) (integrable_const _)
              (fun d ↦ pow_le_pow_left₀ (hVb d).1 (hVb d).2 2)
        _ = h ^ 2 := by simp
    have hV2low : (1 / (1 - γ * qHardP γ)) ^ 2 ≤
        ∫ d, qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N := by
      have h1 := qLbv_auxValue_integral_ge M N γ η hγ' hγ1 hη hrow n (by omega)
      have h2 := qLb_sq_integral_le M N (fun d ↦ qLbvAuxValue γ η (qSamplesExtend M N d) n) 0
      simp only [sub_zero] at h2
      exact (pow_le_pow_left₀ hVh0 h1 2).trans h2
    have hV4up : ∫ d, qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 4 ∂qSamplingLaw M N ≤ h ^ 4 := by
      calc _ ≤ ∫ _d, h ^ 4 ∂qSamplingLaw M N :=
            integral_mono (qSampling_integrable M N _) (integrable_const _)
              (fun d ↦ pow_le_pow_left₀ (hVb d).1 (hVb d).2 4)
        _ = h ^ 4 := by simp
    set m2 := ∫ d, (qLbvXi γ η (qSamplesExtend M N d) n false -
      qLbvXi γ η (qSamplesExtend M N d) n true) ^ 2 ∂qSamplingLaw M N
    have hSV : ∫ d, (qLbvXi γ η (qSamplesExtend M N d) n false -
        qLbvXi γ η (qSamplesExtend M N d) n true) ^ 2 *
        qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N ≤ h ^ 2 * m2 := by
      rw [← integral_const_mul]
      apply integral_mono (qSampling_integrable M N _) (qSampling_integrable M N _)
      intro d
      have := pow_le_pow_left₀ (hVb d).1 (hVb d).2 2
      have h0 := sq_nonneg (qLbvXi γ η (qSamplesExtend M N d) n false -
        qLbvXi γ η (qSamplesExtend M N d) n true)
      simp only
      nlinarith
    have e2 := qLbv_zeta_sq_succ M N γ η hrow n (by omega)
    have e4 := qLbv_zeta_four_succ M N γ η hrow n (by omega)
    rw [← he] at e2 e4
    have hq2def : 2 * (qHardP γ * (1 - qHardP γ)) = q2 := rfl
    rw [hq2def] at e2 e4
    have hγ2 : γ ^ 2 ≤ 1 := by nlinarith
    have hγ20 : 0 ≤ γ ^ 2 := sq_nonneg γ
    refine ⟨?_, ?_, ?_⟩
    · rw [hS2, e2]
      have h1 : (1 - e) ^ 2 * (γ ^ 2 * q2 * (1 / (1 - γ * qHardP γ)) ^ 2 * A) ≤ (1 - e) ^ 2 * m2 :=
        mul_le_mul_of_nonneg_left ih1 (sq_nonneg _)
      have h2 : (e * γ) ^ 2 * q2 * (1 / (1 - γ * qHardP γ)) ^ 2 ≤ (e * γ) ^ 2 * q2 *
          ∫ d, qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N :=
        mul_le_mul_of_nonneg_left hV2low (by positivity)
      have e : γ ^ 2 * q2 * (1 / (1 - γ * qHardP γ)) ^ 2 * ((1 - e) ^ 2 * A + e ^ 2) =
          (1 - e) ^ 2 * (γ ^ 2 * q2 * (1 / (1 - γ * qHardP γ)) ^ 2 * A) +
            (e * γ) ^ 2 * q2 * (1 / (1 - γ * qHardP γ)) ^ 2 := by ring
      linarith
    · rw [hS2, e2]
      have h1 : (1 - e) ^ 2 * m2 ≤ (1 - e) ^ 2 * (ν * A) :=
        mul_le_mul_of_nonneg_left ih2 (sq_nonneg _)
      have h2 : (e * γ) ^ 2 * q2 * ∫ d, qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 2
          ∂qSamplingLaw M N ≤ (e * γ) ^ 2 * q2 * h ^ 2 :=
        mul_le_mul_of_nonneg_left hV2up (by positivity)
      have : ν * ((1 - e) ^ 2 * A + e ^ 2) = (1 - e) ^ 2 * (ν * A) + (e * γ) ^ 2 * q2 * h ^ 2 := by
        simp only [ν]; ring
      linarith
    · rw [hS2, hS4, e4]
      have t1 : 6 * (1 - e) ^ 2 * (e * γ) ^ 2 * q2 * ∫ d, (qLbvXi γ η (qSamplesExtend M N d) n false -
          qLbvXi γ η (qSamplesExtend M N d) n true) ^ 2 *
          qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 2 ∂qSamplingLaw M N ≤
          6 * (1 - e) ^ 2 * e ^ 2 * ν * (ν * A) := by
        have := mul_le_mul_of_nonneg_left (hSV.trans (mul_le_mul_of_nonneg_left ih2
          (by positivity))) (by positivity : (0 : ℝ) ≤ 6 * (1 - e) ^ 2 * (e * γ) ^ 2 * q2)
        calc _ ≤ 6 * (1 - e) ^ 2 * (e * γ) ^ 2 * q2 * (h ^ 2 * (ν * A)) := this
          _ = 6 * (1 - e) ^ 2 * e ^ 2 * ν * (ν * A) := by simp only [ν]; ring
      have t2 : (e * γ) ^ 4 * q2 * ∫ d, qLbvAuxValue γ η (qSamplesExtend M N d) n ^ 4
          ∂qSamplingLaw M N ≤ ν * h ^ 2 * e ^ 4 := by
        have := mul_le_mul_of_nonneg_left hV4up (by positivity : (0 : ℝ) ≤ (e * γ) ^ 4 * q2)
        calc _ ≤ (e * γ) ^ 4 * q2 * h ^ 4 := this
          _ = ν * h ^ 2 * e ^ 4 * γ ^ 2 := by simp only [ν]; ring
          _ ≤ ν * h ^ 2 * e ^ 4 * 1 :=
            mul_le_mul_of_nonneg_left hγ2 (by positivity)
          _ = ν * h ^ 2 * e ^ 4 := by ring
      exact qLbv_scalar_step4 _ _ _ _ ν h A B (1 - e) e rfl ih4 t1 t2

/-- Time-varying Lemma 4.15 (internal form): `E ξ_{t,max} ≥ (5/1536)·min(√(η̄/(1-γ)), 1)` whenever
`t ≤ N` and the weight square sums satisfy `η̄/3 ≤ S₂(t) ≤ η̄` and `S₄(t) ≤ η̄² S₂(t)`. -/
theorem qLbv_xiMax_lower (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1)
    (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) (ηb : ℝ) (hηb : 0 < ηb)
    (hAlow : ηb / 3 ≤ qLbvSq2 η t) (hAup : qLbvSq2 η t ≤ ηb)
    (hB : qLbvSq4 η t ≤ ηb ^ 2 * qLbvSq2 η t) :
    5 / 1536 * min (Real.sqrt (ηb / (1 - γ))) 1 ≤
      ∫ d, qLbvXiMax γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N := by
  have hγ' : (1 : ℝ) / 4 < γ := by linarith
  have hg : 0 < 1 - γ := by linarith
  obtain ⟨hm2, -, hm4⟩ := qLbv_zeta_moment_bounds M N γ η hγ hγ1 hη hrow t ht
  rw [qLbv_integral_xiMax M N γ η hrow t ht]
  set A := qLbvSq2 η t with hAdef
  set m1 := ∫ d, |qLbvXi γ η (qSamplesExtend M N d) t false -
    qLbvXi γ η (qSamplesExtend M N d) t true| ∂qSamplingLaw M N
  set m2 := ∫ d, (qLbvXi γ η (qSamplesExtend M N d) t false -
    qLbvXi γ η (qSamplesExtend M N d) t true) ^ 2 ∂qSamplingLaw M N
  set m4 := ∫ d, (qLbvXi γ η (qSamplesExtend M N d) t false -
    qLbvXi γ η (qSamplesExtend M N d) t true) ^ 4 ∂qSamplingLaw M N
  set h := 1 / (1 - γ) with hh
  have hh0 : 0 < h := by positivity
  have hA0 : 0 ≤ A := qLbvSq2_nonneg η t
  have hpv := qLb_gamma_sq_p_var γ hγ'
  have hVh := qLb_vstar_eq γ hγ' hγ1
  have hν'low : h / 4 ≤ γ ^ 2 * (2 * (qHardP γ * (1 - qHardP γ))) * (1 / (1 - γ * qHardP γ)) ^ 2 := by
    rw [hVh, show γ ^ 2 * (2 * (qHardP γ * (1 - qHardP γ))) =
      2 * (γ ^ 2 * (qHardP γ * (1 - qHardP γ))) by ring, hpv, hh]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    field_simp
    nlinarith
  set ν := γ ^ 2 * (2 * (qHardP γ * (1 - qHardP γ))) * h ^ 2 with hνdef
  have hνup : ν ≤ 2 / 3 * h := by
    rw [hνdef, show γ ^ 2 * (2 * (qHardP γ * (1 - qHardP γ))) =
      2 * (γ ^ 2 * (qHardP γ * (1 - qHardP γ))) by ring, hpv, hh]
    field_simp
    nlinarith
  have hν0 : 0 ≤ ν := by
    have hp := qHardP_bounds γ hγ' hγ1
    have := mul_nonneg hp.1 (by linarith : (0 : ℝ) ≤ 1 - qHardP γ)
    positivity
  set x := ηb / (1 - γ) with hx
  have hxh : x = ηb * h := by rw [hx, hh]; ring
  have hx0 : 0 < x := by positivity
  have hm2x : x / 12 ≤ m2 := by
    rw [hxh]
    exact qLb_scalar_m2 _ A h ηb m2 hν'low hAlow hh0.le hηb.le hm2
  have hm4' : m4 ≤ 3 * ν ^ 2 * A ^ 2 + ν * ηb ^ 2 * h ^ 2 * A := by
    have : ν * h ^ 2 * qLbvSq4 η t ≤ ν * h ^ 2 * (ηb ^ 2 * A) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    have e : ν * h ^ 2 * (ηb ^ 2 * A) = ν * ηb ^ 2 * h ^ 2 * A := by ring
    linarith
  have hm4x : m4 ≤ 4 / 3 * x ^ 2 + 2 / 3 * x ^ 3 := by
    rw [hxh]
    exact hm4'.trans (qLb_scalar_m4 ν A h ηb hν0 hνup hA0 hAup hh0.le hηb.le)
  have hkey : ∀ B : ℝ, 0 < B → m2 ≤ B * m1 + m4 / B ^ 2 := by
    intro B hB0
    have := integral_mono (qSampling_integrable M N _) (qSampling_integrable M N _)
      (fun d ↦ qLb_sq_le_abs_quartic (qLbvXi γ η (qSamplesExtend M N d) t false -
        qLbvXi γ η (qSamplesExtend M N d) t true) B hB0)
    rw [integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
      integral_const_mul, integral_div] at this
    exact this
  have := qLb_scalar_final m1 m2 m4 x hx0 hm2x hm4x hkey
  linarith

/-- Statement (M) for the rescaled linear schedule `η_t = 1/(1 + D t)` with `0 ≤ D ≤ 1`:
`E ξ_{t,max} ≥ (5/1536)·min(√(η_t/(1-γ)), 1)` for `1 ≤ t ≤ N`. The weight hypotheses of
`qLbv_xiMax_lower` are discharged from `(A3)` (`qLbvRate_step`, giving `S₂(t) ≤ η_t` and
`S₄(t) ≤ η_t² S₂(t)`) and `(A4)` (`qLbvSq2_ge`, giving `S₂(t) ≥ η_t/2`). -/
theorem qLbv_xiMax_lower_rescaled (D : ℝ) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (hγ : 3 / 4 ≤ γ)
    (hγ1 : γ < 1) (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ N) :
    5 / 1536 * min (Real.sqrt ((1 / (1 + D * t)) / (1 - γ))) 1 ≤
      ∫ d, qLbvXiMax γ (fun j ↦ 1 / (1 + D * j)) (qSamplesExtend M N d) t ∂qSamplingLaw M N := by
  set r : ℕ → ℝ := fun j ↦ 1 / (1 + D * j) with hr
  have hη : ∀ j, 0 ≤ r j ∧ r j ≤ 1 := qLbvRate_bounds D hD0
  have hstep : ∀ j, (1 - r (j + 1)) * r j ≤ r (j + 1) := qLbvRate_step D hD0 hD1
  have hanti : ∀ j, 1 ≤ j → r (j + 1) ≤ r j := fun j _ ↦ qLbvRate_anti D hD0 j (j + 1) (by omega)
  have h1 : 1 / 2 ≤ r 1 := qLbvRate_one_ge_half D hD0 hD1
  have hlow := qLbvSq2_ge r hη hanti h1 t ht1
  have hup := qLbvSq2_le r hη hstep t
  have hB := qLbvSq4_le r hη hstep t
  have hpos : 0 < r t := qLbvRate_pos D hD0 t
  exact qLbv_xiMax_lower M N γ r hγ hγ1 hη hrow t ht (r t) hpos (by linarith) hup hB

end Moments2

end StatisticalRL.QLearning

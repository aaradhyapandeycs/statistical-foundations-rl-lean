import Formalization.ModelFree.QLearningLowerBoundDefinitions
import Formalization.ModelFree.QLearningLowerBoundProductLaw

/-!
# Auxiliary sequence `Q̂_t`: pathwise bounds, causality, and first moments

Step 5 of the proof of `thm:LB-example-Q-generative`
(`chapters/generative_model_model_free.tex:3316–3420`). The state-1 rows of the MDP are assumed
to be the source rows (`P(1∣1,a) = p`, `P(0∣1,a) = 1-p`), which is checked for `qLbMDP` later.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

/-- The state-1 rows of the source: `P(1∣1,a) = p`, `P(0∣1,a) = 1-p`. -/
def qLbRowSpec (M : DiscountedMDP (Fin 4) Bool) (p : ℝ) : Prop :=
  ∀ (a : Bool) (x : Fin 4), (M.transition 1 a).prob x = if x = 1 then p else if x = 0 then 1 - p else 0

/-! ### Pathwise facts -/

theorem qLbStay_cases (samples : ℕ → Fin 4 → Bool → Fin 4) (s : Fin 4) (k : ℕ) (a : Bool) :
    qLbStay samples s k a = 0 ∨ qLbStay samples s k a = 1 := by
  unfold qLbStay; split <;> simp

theorem qLbStay_nonneg (samples : ℕ → Fin 4 → Bool → Fin 4) (s : Fin 4) (k : ℕ) (a : Bool) :
    0 ≤ qLbStay samples s k a := by
  rcases qLbStay_cases samples s k a with h | h <;> rw [h] <;> norm_num

theorem qLbStay_le_one (samples : ℕ → Fin 4 → Bool → Fin 4) (s : Fin 4) (k : ℕ) (a : Bool) :
    qLbStay samples s k a ≤ 1 := by
  rcases qLbStay_cases samples s k a with h | h <;> rw [h] <;> norm_num

theorem qHardP_bounds (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) :
    0 ≤ qHardP γ ∧ qHardP γ ≤ 1 := by
  unfold qHardP
  exact ⟨div_nonneg (by linarith) (by linarith), by rw [div_le_one (by linarith)]; linarith⟩

theorem qLb_vstar_eq (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) :
    1 / (1 - γ * qHardP γ) = 3 / (4 * (1 - γ)) := by
  have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
  have h1 : 1 - γ * qHardP γ = 4 * (1 - γ) / 3 := by
    unfold qHardP; field_simp; ring
  rw [h1]
  have h2 : (1 : ℝ) - γ ≠ 0 := by intro h; linarith
  field_simp

/-- `γ² p (1-p) = (4γ-1)(1-γ)/9`. -/
theorem qLb_gamma_sq_p_var (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) :
    γ ^ 2 * (qHardP γ * (1 - qHardP γ)) = (4 * γ - 1) * (1 - γ) / 9 := by
  have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
  unfold qHardP; field_simp; ring

/-- Source Lemma `non-negativity-Qt-Vt` for the auxiliary sequence: `0 ≤ Q̂_t(a) ≤ 1/(1-γ)`. -/
theorem qLbAuxIterate_bounds (γ η : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) (a : Bool) :
    0 ≤ qLbAuxIterate γ η samples t a ∧ qLbAuxIterate γ η samples t a ≤ 1 / (1 - γ) := by
  have hg : 0 < 1 - γ := by linarith
  set h := 1 / (1 - γ) with hh
  have hγh : γ * h = h - 1 := by rw [hh]; field_simp; ring
  have hh0 : 0 ≤ h := by positivity
  induction t generalizing a with
  | zero =>
    simp only [qLbAuxIterate]
    rw [qLb_vstar_eq γ hγ hγ1]
    constructor
    · positivity
    · rw [hh, div_le_div_iff₀ (by positivity) hg]; linarith
  | succ t ih =>
    simp only [qLbAuxIterate]
    set V := max (qLbAuxIterate γ η samples t false) (qLbAuxIterate γ η samples t true)
    have hV0 : 0 ≤ V := le_max_of_le_left (ih false).1
    have hV1 : V ≤ h := max_le (ih false).2 (ih true).2
    have hX0 := qLbStay_nonneg samples 1 (t + 1) a
    have hX1 := qLbStay_le_one samples 1 (t + 1) a
    set X := qLbStay samples 1 (t + 1) a
    have hXV0 : 0 ≤ X * V := mul_nonneg hX0 hV0
    have hXV1 : X * V ≤ h := by nlinarith
    have hγ0 : 0 ≤ γ := by linarith
    have h1 : γ * (X * V) ≤ γ * h := mul_le_mul_of_nonneg_left hXV1 hγ0
    have h2 : 0 ≤ γ * (X * V) := mul_nonneg hγ0 hXV0
    have hQ := ih a
    have e1 : 0 ≤ 1 - η := by linarith
    constructor
    · have := mul_nonneg e1 hQ.1
      have := mul_nonneg hη0 (by linarith : (0 : ℝ) ≤ 1 + γ * X * V)
      nlinarith
    · have a1 := mul_le_mul_of_nonneg_left hQ.2 e1
      have a2 : η * (1 + γ * X * V) ≤ η * h := by
        apply mul_le_mul_of_nonneg_left _ hη0
        have : γ * X * V = γ * (X * V) := by ring
        rw [this]; linarith
      nlinarith

theorem qLbAuxValue_bounds (γ η : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) :
    0 ≤ qLbAuxValue γ η samples t ∧ qLbAuxValue γ η samples t ≤ 1 / (1 - γ) :=
  ⟨le_max_of_le_left (qLbAuxIterate_bounds γ η hγ hγ1 hη0 hη1 samples t false).1,
    max_le (qLbAuxIterate_bounds γ η hγ hγ1 hη0 hη1 samples t false).2
      (qLbAuxIterate_bounds γ η hγ hγ1 hη0 hη1 samples t true).2⟩

/-- Two sample streams agree on the state-1 draws at times `1,…,n`. -/
def qLbAgree1 (s s' : ℕ → Fin 4 → Bool → Fin 4) (n : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ n → ∀ a, s k 1 a = s' k 1 a

theorem qLbAuxIterate_congr (γ η : ℝ) (s s' : ℕ → Fin 4 → Bool → Fin 4) (n : ℕ)
    (h : qLbAgree1 s s' n) (t : ℕ) (ht : t ≤ n) :
    qLbAuxIterate γ η s t = qLbAuxIterate γ η s' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext a
    simp only [qLbAuxIterate, qLbStay, ih (by omega), h (t + 1) (by omega) ht a]

theorem qLbAuxValue_congr (γ η : ℝ) (s s' : ℕ → Fin 4 → Bool → Fin 4) (n : ℕ)
    (h : qLbAgree1 s s' n) (t : ℕ) (ht : t ≤ n) :
    qLbAuxValue γ η s t = qLbAuxValue γ η s' t := by
  simp only [qLbAuxValue, qLbAuxIterate_congr γ η s s' n h t ht]

/-- Geometric convolution recursion: `∑_{k=1}^{t+1} c^{t+1-k} f k = c ∑_{k=1}^t c^{t-k} f k + f(t+1)`. -/
theorem qLb_sum_Icc_geom_succ (c : ℝ) (f : ℕ → ℝ) (t : ℕ) :
    ∑ k ∈ Finset.Icc 1 (t + 1), c ^ (t + 1 - k) * f k =
      c * ∑ k ∈ Finset.Icc 1 t, c ^ (t - k) * f k + f (t + 1) := by
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1), Nat.sub_self, pow_zero, one_mul,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := (Finset.mem_Icc.mp hk).2
  rw [show t + 1 - k = (t - k) + 1 by omega, pow_succ]
  ring

/-! ### Product-law moments of the state-1 draws -/

section Moments
variable (M : DiscountedMDP (Fin 4) Bool) (N : ℕ)

theorem qLb_agree1_of_past (n : ℕ) (d d' : QSamples (Fin 4) Bool N)
    (h : ∀ i : (Fin 4 × Bool) × Fin N, i.2.val < n → d i = d' i) :
    qLbAgree1 (qSamplesExtend M N d) (qSamplesExtend M N d') n :=
  fun k _ hk a ↦ qSamplesExtend_agree_past M N n d d' h k hk 1 a

/-- A function of the state-1 draws at times `≤ n` is uncorrelated with a function of the two
state-1 draws at time `n+1`. -/
theorem qLb_integral_mul_state1 (n : ℕ) (F : QSamples (Fin 4) Bool N → ℝ)
    (hF : ∀ d d', qLbAgree1 (qSamplesExtend M N d) (qSamplesExtend M N d') n → F d = F d')
    (g : Fin 4 → Fin 4 → ℝ) :
    ∫ d, F d * g (qSamplesExtend M N d (n + 1) 1 false) (qSamplesExtend M N d (n + 1) 1 true)
        ∂qSamplingLaw M N =
      (∫ d, F d ∂qSamplingLaw M N) *
        ∫ d, g (qSamplesExtend M N d (n + 1) 1 false) (qSamplesExtend M N d (n + 1) 1 true)
          ∂qSamplingLaw M N := by
  apply qLb_integral_mul_past_layer M N n F
  · intro d d' h
    exact hF d d' (qLb_agree1_of_past M N n d d' h)
  · intro d d' h
    rw [qSamplesExtend_agree_layer M N n d d' h, qSamplesExtend_agree_layer M N n d d' h]

variable (γ : ℝ)

theorem qLb_integral_state1 (hrow : qLbRowSpec M (qHardP γ)) (k : ℕ) (hk1 : 1 ≤ k)
    (hkN : k ≤ N) (a : Bool) (g : Fin 4 → ℝ) :
    ∫ d, g (qSamplesExtend M N d k 1 a) ∂qSamplingLaw M N =
      qHardP γ * g 1 + (1 - qHardP γ) * g 0 := by
  simp_rw [qSamplesExtend_coord M N k hk1 hkN]
  rw [qLb_integral_coord]
  simp only [Fin.sum_univ_four, hrow a]
  simp
  ring

theorem qLb_integral_state1_pair (hrow : qLbRowSpec M (qHardP γ)) (k : ℕ) (hk1 : 1 ≤ k)
    (hkN : k ≤ N) (f g : Fin 4 → ℝ) :
    ∫ d, f (qSamplesExtend M N d k 1 false) * g (qSamplesExtend M N d k 1 true)
        ∂qSamplingLaw M N =
      (qHardP γ * f 1 + (1 - qHardP γ) * f 0) * (qHardP γ * g 1 + (1 - qHardP γ) * g 0) := by
  rw [← qLb_integral_state1 M N γ hrow k hk1 hkN false f,
    ← qLb_integral_state1 M N γ hrow k hk1 hkN true g]
  simp_rw [qSamplesExtend_coord M N k hk1 hkN]
  apply qLb_integral_two_coords
  simp

/-- Indicator of a stay. -/
def qLbInd (x : Fin 4) : ℝ := if x = 1 then 1 else 0

/-- The difference `D = P_k(1∣1,1) - P_k(1∣1,2)` as a function of the two draws. -/
def qLbD (x y : Fin 4) : ℝ := qLbInd x - qLbInd y

theorem qLbD_cube (x y : Fin 4) : qLbD x y ^ 3 = qLbD x y := by
  unfold qLbD qLbInd; split_ifs <;> norm_num

theorem qLbD_four (x y : Fin 4) : qLbD x y ^ 4 = qLbD x y ^ 2 := by
  unfold qLbD qLbInd; split_ifs <;> norm_num

theorem qLbD_sq (x y : Fin 4) : qLbD x y ^ 2 = qLbInd x * 1 + 1 * qLbInd y - 2 * (qLbInd x * qLbInd y) := by
  unfold qLbD qLbInd; split_ifs <;> norm_num

theorem qLb_integral_D (hrow : qLbRowSpec M (qHardP γ)) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    ∫ d, qLbD (qSamplesExtend M N d k 1 false) (qSamplesExtend M N d k 1 true)
      ∂qSamplingLaw M N = 0 := by
  unfold qLbD
  rw [integral_sub (qSampling_integrable M N _) (qSampling_integrable M N _),
    qLb_integral_state1 M N γ hrow k hk1 hkN false qLbInd,
    qLb_integral_state1 M N γ hrow k hk1 hkN true qLbInd]
  ring

theorem qLb_integral_D_sq (hrow : qLbRowSpec M (qHardP γ)) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    ∫ d, qLbD (qSamplesExtend M N d k 1 false) (qSamplesExtend M N d k 1 true) ^ 2
      ∂qSamplingLaw M N = 2 * (qHardP γ * (1 - qHardP γ)) := by
  simp_rw [qLbD_sq]
  rw [integral_sub (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    qLb_integral_state1_pair M N γ hrow k hk1 hkN qLbInd (fun _ ↦ 1),
    qLb_integral_state1_pair M N γ hrow k hk1 hkN (fun _ ↦ 1) qLbInd,
    integral_const_mul,
    qLb_integral_state1_pair M N γ hrow k hk1 hkN qLbInd qLbInd]
  simp [qLbInd]
  ring

/-- `E[F · (P_{n+1}(1∣1,a) - p)] = 0` for a function `F` of the draws at times `≤ n`. -/
theorem qLb_integral_mul_centered (hrow : qLbRowSpec M (qHardP γ)) (n : ℕ) (hn : n + 1 ≤ N)
    (F : QSamples (Fin 4) Bool N → ℝ)
    (hF : ∀ d d', qLbAgree1 (qSamplesExtend M N d) (qSamplesExtend M N d') n → F d = F d')
    (a : Bool) :
    ∫ d, F d * (qLbStay (qSamplesExtend M N d) 1 (n + 1) a - qHardP γ) ∂qSamplingLaw M N = 0 := by
  have key := qLb_integral_mul_state1 M N n F hF
    (fun x y ↦ (if a then qLbInd y else qLbInd x) - qHardP γ)
  have hpt : ∀ d : QSamples (Fin 4) Bool N,
      qLbStay (qSamplesExtend M N d) 1 (n + 1) a =
        if a then qLbInd (qSamplesExtend M N d (n + 1) 1 true)
        else qLbInd (qSamplesExtend M N d (n + 1) 1 false) := by
    intro d; cases a <;> simp [qLbStay, qLbInd]
  simp_rw [hpt]
  rw [key]
  have hg : ∫ d, ((if a then qLbInd (qSamplesExtend M N d (n + 1) 1 true)
      else qLbInd (qSamplesExtend M N d (n + 1) 1 false)) - qHardP γ) ∂qSamplingLaw M N = 0 := by
    rw [integral_sub (qSampling_integrable M N _) (integrable_const _)]
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [qLb_integral_state1 M N γ hrow (n + 1) (by omega) hn false qLbInd]
      simp [qLbInd]
    · simp only [↓reduceIte]
      rw [qLb_integral_state1 M N γ hrow (n + 1) (by omega) hn true qLbInd]
      simp [qLbInd]
  rw [hg, mul_zero]

variable (η : ℝ)

/-- `E[V̂_t] ≥ V⋆(1) = 1/(1-γp)` for every `t ≤ N`: the auxiliary sequence over-estimates on
average (proof via `E Q̂_t(1) ≥ V⋆(1)` and `V̂_t ≥ Q̂_t(1)`). -/
theorem qLb_auxIterate_integral_ge (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) :
    1 / (1 - γ * qHardP γ) ≤
      ∫ d, qLbAuxIterate γ η (qSamplesExtend M N d) t false ∂qSamplingLaw M N := by
  have hp := qHardP_bounds γ hγ hγ1
  set Vh := 1 / (1 - γ * qHardP γ) with hVh
  have hVfix : 1 + γ * qHardP γ * Vh = Vh := by
    have h1 : 1 - γ * qHardP γ ≠ 0 := by
      rw [show 1 - γ * qHardP γ = 4 * (1 - γ) / 3 by
        have hγ0 : γ ≠ 0 := by intro h; rw [h] at hγ; norm_num at hγ
        unfold qHardP; field_simp; ring]
      intro h; linarith
    rw [hVh]; field_simp; ring
  induction t with
  | zero => simp [qLbAuxIterate, Vh]
  | succ t ih =>
    have ih' := ih (by omega)
    have hV : ∫ d, qLbAuxIterate γ η (qSamplesExtend M N d) t false ∂qSamplingLaw M N ≤
        ∫ d, qLbAuxValue γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N :=
      integral_mono (qSampling_integrable M N _) (qSampling_integrable M N _)
        (fun d ↦ le_max_left _ _)
    have hpt : ∀ d : QSamples (Fin 4) Bool N,
        qLbAuxIterate γ η (qSamplesExtend M N d) (t + 1) false =
          (1 - η) * qLbAuxIterate γ η (qSamplesExtend M N d) t false + η * (1 + γ * qHardP γ *
            qLbAuxValue γ η (qSamplesExtend M N d) t) +
          (η * γ) * (qLbAuxValue γ η (qSamplesExtend M N d) t *
            (qLbStay (qSamplesExtend M N d) 1 (t + 1) false - qHardP γ)) := by
      intro d; simp only [qLbAuxIterate, qLbAuxValue]; ring
    have hcent := qLb_integral_mul_centered M N γ hrow t ht
      (fun d ↦ qLbAuxValue γ η (qSamplesExtend M N d) t)
      (fun d d' h ↦ qLbAuxValue_congr γ η _ _ t h t le_rfl) false
    simp_rw [hpt]
    rw [integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
      integral_const_mul, hcent, integral_add (qSampling_integrable M N _)
        (qSampling_integrable M N _), integral_const_mul, integral_const_mul,
      integral_add (integrable_const _) (qSampling_integrable M N _), integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
    have hη' : 0 ≤ 1 - η := by linarith
    have hγp : 0 ≤ γ * qHardP γ := mul_nonneg (by linarith) hp.1
    nlinarith [mul_le_mul_of_nonneg_left ih' hη', mul_nonneg hη0 hγp,
      mul_le_mul_of_nonneg_left (ih'.trans hV) (mul_nonneg hη0 hγp)]

theorem qLb_auxValue_integral_ge (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) :
    1 / (1 - γ * qHardP γ) ≤ ∫ d, qLbAuxValue γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N :=
  (qLb_auxIterate_integral_ge M N γ η hγ hγ1 hη0 hη1 hrow t ht).trans
    (integral_mono (qSampling_integrable M N _) (qSampling_integrable M N _)
      (fun d ↦ le_max_left _ _))

/-- `E[ξ_t(a)] = 0` for `t ≤ N`. -/
theorem qLb_integral_xi (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) (a : Bool) :
    ∫ d, qLbXi γ η (qSamplesExtend M N d) t a ∂qSamplingLaw M N = 0 := by
  unfold qLbXi
  rw [integral_finset_sum _ (fun k _ ↦ qSampling_integrable M N _)]
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨hk1, hkt⟩ := Finset.mem_Icc.mp hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hpt : ∀ d : QSamples (Fin 4) Bool N,
      η * (1 - η) ^ (t - (n + 1)) * γ * (qLbStay (qSamplesExtend M N d) 1 (n + 1) a - qHardP γ) *
        qLbAuxValue γ η (qSamplesExtend M N d) (n + 1 - 1) =
      (η * (1 - η) ^ (t - (n + 1)) * γ) * (qLbAuxValue γ η (qSamplesExtend M N d) n *
        (qLbStay (qSamplesExtend M N d) 1 (n + 1) a - qHardP γ)) := by
    intro d; simp only [Nat.add_sub_cancel]; ring
  simp_rw [hpt]
  rw [integral_const_mul, qLb_integral_mul_centered M N γ hrow n (by omega)
    (fun d ↦ qLbAuxValue γ η (qSamplesExtend M N d) n)
    (fun d d' h ↦ qLbAuxValue_congr γ η _ _ n h n le_rfl) a, mul_zero]

theorem qLb_max_eq (x y : ℝ) : max x y = (x + y + |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring

/-- `E[ξ_{t,max}] = E|ξ_t(1) - ξ_t(2)|/2`. -/
theorem qLb_integral_xiMax (hrow : qLbRowSpec M (qHardP γ)) (t : ℕ) (ht : t ≤ N) :
    ∫ d, qLbXiMax γ η (qSamplesExtend M N d) t ∂qSamplingLaw M N =
      (∫ d, |qLbXi γ η (qSamplesExtend M N d) t false - qLbXi γ η (qSamplesExtend M N d) t true|
        ∂qSamplingLaw M N) / 2 := by
  unfold qLbXiMax
  simp_rw [qLb_max_eq]
  rw [integral_div, integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    integral_add (qSampling_integrable M N _) (qSampling_integrable M N _),
    qLb_integral_xi M N γ η hrow t ht false, qLb_integral_xi M N γ η hrow t ht true]
  ring

end Moments

end StatisticalRL.QLearning

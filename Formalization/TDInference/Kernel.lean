import Formalization.TDInference.Linearised

/-!
# Theorem 7.11 support (M5): kernel bounds for the linearised TD process (B1, B2, F2)

Source: `chapters/inference.tex:104–117` (`A = diag(μ)(I − γP_π)`), :134 (`η_t = η₀ t^{-2/3}`).
Objects of `TDInference/Linearised.lean`; `e_k = η'_k = stepSize η₀ (k+1)`,
`a = μmin (1−γ)`, `u_T = T^{1/3}` (`natCubeRoot`).

Generic scalar part (any sequence `e` with `0 ≤ a e_i ≤ 1`):
* `contrProd a e m t = ∏_{i ∈ [m,t)} (1 − a e_i)`, `contrSum a e T k = ∑_{t ∈ [k,T)} p_{k+1,t+1}`,
  `contrDrift a e T k = ∑_{t ∈ [k,T)} (e_k − e_{t+1}) p_{k+1,t+1}`.
* `mul_contrSum_le`: if `e` is antitone, `e ≤ E`, `e_{t₁} > 0` and the schedule varies slowly
  after `t₁` (`e_k − e_{k+1} ≤ (a/2) e_{k+1} e_k`), then `e_k σ_k ≤ E t₁ + 3E/(a e_{t₁})` for all
  `k` and `T` (backward induction on `σ_k = 1 + (1 − a e_{k+1}) σ_{k+1}`).
* `contrDrift_le`: `τ_k ≤ K/(k+2) · σ_k` when `(e_k − e_{k+1})(k+2) ≤ e_k` and `e_k σ_k ≤ K`
  (`τ_k = (e_k − e_{k+1}) σ_k + (1 − a e_{k+1}) τ_{k+1}`).
* `mul_sum_contrProd_le`: `a e_{T−1} ∑_{k<T} p_{k+1,T} ≤ 1` (telescoping).

TD part:
* `norm_linStep_mulVec_le` (B1): `‖(I − η'_t A) v‖_∞ ≤ (1 − a η'_t) ‖v‖_∞` for `0 ≤ η₀ ≤ 1`
  and every full-support `μ` (no stationarity).
* `norm_linKernel_mulVec_le` (B2): `‖G_{m,t} v‖_∞ ≤ p_{m,t} ‖v‖_∞`.
* `norm_linWeight_mulVec_le` (B2, F1): `‖linWeight T k v‖_∞ ≤ K_β ‖v‖_∞` with the k- and T-free
  `K_β = linWeightConst = η₀ t₁ + 3η₀/(a η_{t₁+1})`, `t₁ = tdBurnIn`.
* `tdA_mul_sum_linKernel` (F2): `A ∑_{t ∈ [k,T)} η'_{t+1} G_{k+1,t+1} = I − G_{k+1,T+1}`, hence
  `linWeight_sub_inv_eq`: `linWeight T k − A⁻¹ = ∑_t (η'_k − η'_{t+1}) G_{k+1,t+1} − A⁻¹ G_{k+1,T+1}`.
* `norm_linWeight_sub_inv_mulVec_le` and `sum_linWeightGap_le`:
  `∑_{k<T} (τ_k + p_{k+1,T+1}/a) ≤ (3K_β² + 1/a²) u_T²/η₀`.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

/-! ## Generic scalar products and sums -/

section Scalar

variable (a : ℝ) (e : ℕ → ℝ)

/-- `p_{m,t} = ∏_{i ∈ [m,t)} (1 − a e_i)`. -/
noncomputable def contrProd (m t : ℕ) : ℝ := ∏ i ∈ Ico m t, (1 - a * e i)

/-- `σ_k = ∑_{t ∈ [k,T)} p_{k+1,t+1}`. -/
noncomputable def contrSum (T k : ℕ) : ℝ := ∑ t ∈ Ico k T, contrProd a e (k + 1) (t + 1)

/-- `τ_k = ∑_{t ∈ [k,T)} (e_k − e_{t+1}) p_{k+1,t+1}`. -/
noncomputable def contrDrift (T k : ℕ) : ℝ :=
  ∑ t ∈ Ico k T, (e k - e (t + 1)) * contrProd a e (k + 1) (t + 1)

variable {a e}

theorem contrProd_self (m : ℕ) : contrProd a e m m = 1 := by simp [contrProd]

theorem contrProd_nonneg (h1 : ∀ i, a * e i ≤ 1) (m t : ℕ) : 0 ≤ contrProd a e m t :=
  prod_nonneg fun i _ ↦ sub_nonneg.2 (h1 i)

theorem contrProd_le_one (h0 : ∀ i, 0 ≤ a * e i) (h1 : ∀ i, a * e i ≤ 1) (m t : ℕ) :
    contrProd a e m t ≤ 1 :=
  prod_le_one (fun i _ ↦ sub_nonneg.2 (h1 i)) fun i _ ↦ by linarith [h0 i]

theorem contrProd_succ_bot {m t : ℕ} (h : m < t) :
    contrProd a e m t = (1 - a * e m) * contrProd a e (m + 1) t :=
  prod_eq_prod_Ico_succ_bot h _

theorem contrProd_succ_top {m t : ℕ} (h : m ≤ t) :
    contrProd a e m (t + 1) = contrProd a e m t * (1 - a * e t) :=
  prod_Ico_succ_top h _

theorem contrSum_of_le {T k : ℕ} (h : T ≤ k) : contrSum a e T k = 0 := by
  simp [contrSum, Ico_eq_empty_of_le h]

theorem contrDrift_of_le {T k : ℕ} (h : T ≤ k) : contrDrift a e T k = 0 := by
  simp [contrDrift, Ico_eq_empty_of_le h]

theorem contrSum_nonneg (h1 : ∀ i, a * e i ≤ 1) (T k : ℕ) : 0 ≤ contrSum a e T k :=
  sum_nonneg fun _ _ ↦ contrProd_nonneg h1 _ _

theorem contrSum_succ {T k : ℕ} (hk : k < T) :
    contrSum a e T k = 1 + (1 - a * e (k + 1)) * contrSum a e T (k + 1) := by
  rw [contrSum, sum_eq_sum_Ico_succ_bot hk, contrProd_self, contrSum, mul_sum]
  congr 1
  refine sum_congr rfl fun t ht ↦ ?_
  exact contrProd_succ_bot (by simp at ht; omega)

theorem contrDrift_succ {T k : ℕ} (hk : k < T) :
    contrDrift a e T k = (e k - e (k + 1)) * contrSum a e T k +
      (1 - a * e (k + 1)) * contrDrift a e T (k + 1) := by
  have hsplit : contrDrift a e T k = (e k - e (k + 1)) * contrSum a e T k +
      ∑ t ∈ Ico k T, (e (k + 1) - e (t + 1)) * contrProd a e (k + 1) (t + 1) := by
    rw [contrDrift, contrSum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun t _ ↦ by ring
  rw [hsplit, sum_eq_sum_Ico_succ_bot hk, sub_self, zero_mul, zero_add, contrDrift, mul_sum]
  congr 1
  refine sum_congr rfl fun t ht ↦ ?_
  rw [contrProd_succ_bot (by simp at ht; omega)]
  ring

theorem contrSum_le_succ (h0 : ∀ i, 0 ≤ a * e i) (h1 : ∀ i, a * e i ≤ 1) (T k : ℕ) :
    contrSum a e T k ≤ 1 + contrSum a e T (k + 1) := by
  have hs := contrSum_nonneg h1 T (k + 1)
  by_cases hk : k < T
  · rw [contrSum_succ hk]
    nlinarith [h0 (k + 1)]
  · rw [contrSum_of_le (not_lt.1 hk)]
    linarith

/-- Before the burn-in: `σ_k ≤ (t₁ − k) + σ_{t₁}`. -/
theorem contrSum_le_add (h0 : ∀ i, 0 ≤ a * e i) (h1 : ∀ i, a * e i ≤ 1) (T t₁ : ℕ) :
    ∀ j k, k + j = t₁ → contrSum a e T k ≤ j + contrSum a e T t₁ := by
  intro j
  induction j with
  | zero => intro k hk; simp only [add_zero] at hk; subst hk; simp
  | succ j ih =>
    intro k hk
    have := ih (k + 1) (by omega)
    have := contrSum_le_succ h0 h1 T k
    push_cast
    linarith

/-- After the burn-in: `e_k σ_k ≤ 3/a`. -/
theorem mul_contrSum_le_of_ge (ha : 0 < a) (he0 : ∀ i, 0 ≤ e i) (h1 : ∀ i, a * e i ≤ 1)
    (hanti : ∀ i, e (i + 1) ≤ e i) {t₁ : ℕ}
    (hslow : ∀ k, t₁ ≤ k → e k - e (k + 1) ≤ a / 2 * e (k + 1) * e k) (T : ℕ) :
    ∀ j k, t₁ ≤ k → T ≤ k + j → e k * contrSum a e T k ≤ 3 / a := by
  have h3a : 0 ≤ 3 / a := by positivity
  intro j
  induction j with
  | zero =>
    intro k _ hT
    rw [contrSum_of_le (by omega), mul_zero]; exact h3a
  | succ j ih =>
    intro k hk hT
    by_cases hkT : T ≤ k
    · rw [contrSum_of_le hkT, mul_zero]; exact h3a
    push_neg at hkT
    have hIH := ih (k + 1) (by omega) (by omega)
    rw [contrSum_succ hkT]
    set x := e k
    set y := e (k + 1)
    set σ := contrSum a e T (k + 1)
    have hσ : 0 ≤ σ := contrSum_nonneg h1 T (k + 1)
    have hy0 : 0 ≤ y := he0 (k + 1)
    have hyx : y ≤ x := hanti k
    have hsl : x - y ≤ a / 2 * y * x := hslow k hk
    have hax : a * x ≤ 1 := h1 k
    have hay : a * y ≤ 1 := h1 (k + 1)
    -- `x (1 − a y) ≤ y (1 − (a/2) y)`
    have hxy : x * (1 - a * y) ≤ y * (1 - a / 2 * y) := by
      nlinarith [mul_le_mul_of_nonneg_left hyx (mul_nonneg ha.le hy0)]
    -- `x ≤ (3/2) y`
    have hx32 : x ≤ 3 / 2 * y := by nlinarith [mul_le_mul_of_nonneg_left hax hy0]
    have hc : 0 ≤ 1 - a / 2 * y := by nlinarith
    calc x * (1 + (1 - a * y) * σ) = x + x * (1 - a * y) * σ := by ring
      _ ≤ x + y * (1 - a / 2 * y) * σ := by nlinarith [mul_le_mul_of_nonneg_right hxy hσ]
      _ = x + (1 - a / 2 * y) * (y * σ) := by ring
      _ ≤ x + (1 - a / 2 * y) * (3 / a) := by nlinarith [mul_le_mul_of_nonneg_left hIH hc]
      _ = x - 3 / 2 * y + 3 / a := by have ha' := ha.ne'; field_simp; ring
      _ ≤ 3 / a := by linarith

/-- **Uniform weight bound**: `e_k σ_k ≤ E t₁ + 3E/(a e_{t₁})` for all `k` and `T`. -/
theorem mul_contrSum_le (ha : 0 < a) (he0 : ∀ i, 0 ≤ e i) (h1 : ∀ i, a * e i ≤ 1)
    (hanti : ∀ i, e (i + 1) ≤ e i) {E : ℝ} (hE : ∀ i, e i ≤ E) {t₁ : ℕ} (ht₁ : 0 < e t₁)
    (hslow : ∀ k, t₁ ≤ k → e k - e (k + 1) ≤ a / 2 * e (k + 1) * e k) (T k : ℕ) :
    e k * contrSum a e T k ≤ E * t₁ + 3 * E / (a * e t₁) := by
  have h0 : ∀ i, 0 ≤ a * e i := fun i ↦ mul_nonneg ha.le (he0 i)
  have hlate := mul_contrSum_le_of_ge ha he0 h1 hanti hslow T T
  have hE0 : 0 ≤ E := (he0 0).trans (hE 0)
  have hEt : e t₁ ≤ E := hE t₁
  have h3 : 3 / a ≤ 3 * E / (a * e t₁) := by
    rw [div_le_div_iff₀ ha (mul_pos ha ht₁)]
    nlinarith [mul_le_mul_of_nonneg_left hEt ha.le]
  have hEt₁ : 0 ≤ E * t₁ := mul_nonneg hE0 (Nat.cast_nonneg _)
  by_cases hk : t₁ ≤ k
  · exact (hlate k hk (by omega)).trans (by linarith)
  push_neg at hk
  have hσ₁ : contrSum a e T t₁ ≤ 3 / (a * e t₁) := by
    have := hlate t₁ le_rfl (by omega)
    rw [le_div_iff₀ (mul_pos ha ht₁)]
    rw [le_div_iff₀ ha] at this
    nlinarith
  have hearly := contrSum_le_add h0 h1 T t₁ (t₁ - k) k (by omega)
  have hσk := contrSum_nonneg h1 T k
  have hcast : ((t₁ - k : ℕ) : ℝ) ≤ t₁ := by exact_mod_cast Nat.sub_le t₁ k
  calc e k * contrSum a e T k ≤ E * contrSum a e T k := mul_le_mul_of_nonneg_right (hE k) hσk
    _ ≤ E * (t₁ + 3 / (a * e t₁)) := by
        refine mul_le_mul_of_nonneg_left ?_ hE0
        linarith
    _ = E * t₁ + 3 * E / (a * e t₁) := by ring

/-- `τ_k ≤ K/(k+2) · σ_k`. -/
theorem contrDrift_le {T : ℕ} (h1 : ∀ i, a * e i ≤ 1)
    (hd : ∀ k : ℕ, (e k - e (k + 1)) * ((k : ℝ) + 2) ≤ e k) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ k, e k * contrSum a e T k ≤ K) :
    ∀ j k, T ≤ k + j → contrDrift a e T k ≤ K / ((k : ℝ) + 2) * contrSum a e T k := by
  intro j
  induction j with
  | zero =>
    intro k hT
    rw [contrDrift_of_le (by omega), contrSum_of_le (by omega), mul_zero]
  | succ j ih =>
    intro k hT
    by_cases hkT : T ≤ k
    · rw [contrDrift_of_le hkT, contrSum_of_le hkT, mul_zero]
    push_neg at hkT
    have hIH := ih (k + 1) (by omega)
    have hσ := contrSum_nonneg h1 T k
    have hσ1 := contrSum_nonneg h1 T (k + 1)
    have hc : 0 ≤ 1 - a * e (k + 1) := sub_nonneg.2 (h1 _)
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hmono : K / (((k + 1 : ℕ) : ℝ) + 2) ≤ K / ((k : ℝ) + 2) := by
      apply div_le_div_of_nonneg_left hK0 hk2
      push_cast; linarith
    have hdσ : (e k - e (k + 1)) * contrSum a e T k ≤ K / ((k : ℝ) + 2) := by
      rw [le_div_iff₀ hk2]
      have := mul_le_mul_of_nonneg_right (hd k) hσ
      nlinarith [hK k]
    have hrec := contrSum_succ (a := a) (e := e) hkT
    rw [contrDrift_succ hkT]
    calc (e k - e (k + 1)) * contrSum a e T k + (1 - a * e (k + 1)) * contrDrift a e T (k + 1)
        ≤ K / ((k : ℝ) + 2) + (1 - a * e (k + 1)) *
            (K / ((k : ℝ) + 2) * contrSum a e T (k + 1)) := by
          refine add_le_add hdσ (mul_le_mul_of_nonneg_left (hIH.trans ?_) hc)
          exact mul_le_mul_of_nonneg_right hmono hσ1
      _ = K / ((k : ℝ) + 2) * contrSum a e T k := by rw [hrec]; ring

/-- Telescoping: `a e_{T−1} ∑_{k<T} p_{k+1,T} ≤ 1` for an antitone `e`. -/
theorem mul_sum_contrProd_le (ha : 0 ≤ a) (h1 : ∀ i, a * e i ≤ 1)
    (hanti : ∀ i, e (i + 1) ≤ e i) {T : ℕ} (hT : 1 ≤ T) :
    a * e (T - 1) * ∑ k ∈ range T, contrProd a e (k + 1) T ≤ 1 := by
  have hantimono : ∀ i j, i ≤ j → e j ≤ e i := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih => exact (hanti j).trans ih
  have hstep : ∀ k ∈ range T, a * e (T - 1) * contrProd a e (k + 1) T ≤
      contrProd a e (k + 1) T - contrProd a e k T := by
    intro k hk
    have hkT : k < T := mem_range.1 hk
    rw [contrProd_succ_bot hkT]
    have := contrProd_nonneg h1 (k + 1) T
    have : a * e (T - 1) ≤ a * e k := mul_le_mul_of_nonneg_left (hantimono k (T - 1) (by omega)) ha
    nlinarith
  calc a * e (T - 1) * ∑ k ∈ range T, contrProd a e (k + 1) T
      = ∑ k ∈ range T, a * e (T - 1) * contrProd a e (k + 1) T := mul_sum _ _ _
    _ ≤ ∑ k ∈ range T, (contrProd a e (k + 1) T - contrProd a e k T) := sum_le_sum hstep
    _ = contrProd a e T T - contrProd a e 0 T := sum_range_sub (fun k ↦ contrProd a e k T) T
    _ ≤ 1 := by rw [contrProd_self]; linarith [contrProd_nonneg h1 0 T]

end Scalar

/-! ## The TD step size and contraction -/

variable {State Action : Type} [Fintype State] [Fintype Action]

theorem mumin_le_one (μ : FiniteDistribution State) {μmin : ℝ} (hμmin : ∀ s, μmin ≤ μ.prob s) :
    μmin ≤ 1 := by
  rcases isEmpty_or_nonempty State with hS | hS
  · have := μ.sum_prob
    simp at this
  · obtain ⟨s⟩ := hS
    exact (hμmin s).trans (prob_le_one μ s)

/-- The contraction rate `a = μmin (1−γ)`. -/
noncomputable def linRate (M : DiscountedMDP State Action) (μmin : ℝ) : ℝ :=
  μmin * (1 - M.discount)

theorem linRate_pos (M : DiscountedMDP State Action) {μmin : ℝ} (hμmin0 : 0 < μmin) :
    0 < linRate M μmin :=
  mul_pos hμmin0 (by linarith [M.discount_lt_one])

theorem linRate_le_one (M : DiscountedMDP State Action) (μ : FiniteDistribution State)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) : linRate M μmin ≤ 1 := by
  have := mumin_le_one μ hμmin
  have := M.discount_nonneg
  unfold linRate; nlinarith

theorem stepSize_succ_le_one {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (t : ℕ) :
    stepSize η₀ (t + 1) ≤ 1 :=
  (stepSize_le h0 (Nat.le_add_left 1 t)).trans h1

theorem linRate_mul_stepSize_le (M : DiscountedMDP State Action) (μ : FiniteDistribution State)
    {μmin η₀ : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (h0 : 0 ≤ η₀)
    (h1 : η₀ ≤ 1) (t : ℕ) : linRate M μmin * stepSize η₀ (t + 1) ≤ 1 := by
  have ha := linRate_le_one M μ hμmin0 hμmin
  have ha0 := (linRate_pos M hμmin0).le
  have := stepSize_succ_le_one h0 h1 t
  have := stepSize_nonneg h0 (t + 1)
  nlinarith

/-- **B1 (sup-norm contraction).** For `0 ≤ η₀ ≤ 1` and every full-support `μ`,
`‖(I − η'_t A) v‖_∞ ≤ (1 − μmin(1−γ)η'_t) ‖v‖_∞`. -/
theorem norm_linStep_mulVec_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (t : ℕ)
    (v : State → ℝ) :
    ‖linStep M π μ η₀ t *ᵥ v‖ ≤ (1 - linRate M μmin * stepSize η₀ (t + 1)) * ‖v‖ := by
  set η := stepSize η₀ (t + 1)
  have hη0 : 0 ≤ η := stepSize_nonneg h0 _
  have hη1 : η ≤ 1 := stepSize_succ_le_one h0 h1 t
  have hγ0 := M.discount_nonneg
  have hγ1 : 0 ≤ 1 - M.discount := by linarith [M.discount_lt_one]
  have hv0 := norm_nonneg v
  refine (pi_norm_le_iff_of_nonneg ?_).2 fun s ↦ ?_
  · have := linRate_mul_stepSize_le M μ hμmin0 hμmin h0 h1 t
    nlinarith
  have hμs := μ.prob_nonneg s
  have hμ1 := prob_le_one μ s
  have hE : |(M.policyTransition π s).expectation v| ≤ ‖v‖ :=
    (M.policyTransition π s).abs_expectation_le fun s' ↦ abs_apply_le_norm v s'
  have hvs := abs_apply_le_norm v s
  have happ : (linStep M π μ η₀ t *ᵥ v) s =
      (1 - η * μ.prob s) * v s + η * μ.prob s * M.discount *
        (M.policyTransition π s).expectation v := by
    simp only [linStep, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, tdA_mulVec_apply]
    ring
  rw [Real.norm_eq_abs, happ]
  have hc1 : 0 ≤ 1 - η * μ.prob s := by nlinarith
  have hc2 : 0 ≤ η * μ.prob s * M.discount := by positivity
  calc |(1 - η * μ.prob s) * v s + η * μ.prob s * M.discount *
        (M.policyTransition π s).expectation v|
      ≤ (1 - η * μ.prob s) * |v s| + η * μ.prob s * M.discount *
          |(M.policyTransition π s).expectation v| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hc1, abs_of_nonneg hc2]
    _ ≤ (1 - η * μ.prob s) * ‖v‖ + η * μ.prob s * M.discount * ‖v‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hvs hc1) (mul_le_mul_of_nonneg_left hE hc2)
    _ = (1 - η * μ.prob s * (1 - M.discount)) * ‖v‖ := by ring
    _ ≤ (1 - linRate M μmin * η) * ‖v‖ := by
        refine mul_le_mul_of_nonneg_right ?_ hv0
        unfold linRate
        nlinarith [mul_le_mul_of_nonneg_right (hμmin s) (mul_nonneg hη0 hγ1)]

/-- The scalar sequence `e_k = η'_k = stepSize η₀ (k+1)`. -/
noncomputable def linStepSeq (η₀ : ℝ) (k : ℕ) : ℝ := stepSize η₀ (k + 1)

/-- **B2 (kernel decay).** `‖G_{m,t} v‖_∞ ≤ p_{m,t} ‖v‖_∞` with `p_{m,t} = ∏_{i∈[m,t)}(1 − aη'_i)`. -/
theorem norm_linKernel_mulVec_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (m t : ℕ) (v : State → ℝ) :
    ‖linKernel M π μ η₀ m t *ᵥ v‖ ≤
      contrProd (linRate M μmin) (linStepSeq η₀) m t * ‖v‖ :=
  norm_matProd_mulVec_le _ _
    (fun i ↦ sub_nonneg.2 (linRate_mul_stepSize_le M μ hμmin0 hμmin h0 h1 i))
    (fun i v ↦ norm_linStep_mulVec_le M π μ h0 h1 hμmin0 hμmin i v) m t v

theorem contrDrift_linStepSeq_nonneg {η₀ μmin : ℝ} (h0 : 0 ≤ η₀)
    {M : DiscountedMDP State Action} {μ : FiniteDistribution State} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) (h1 : η₀ ≤ 1) (T k : ℕ) :
    0 ≤ contrDrift (linRate M μmin) (linStepSeq η₀) T k := by
  refine sum_nonneg fun t ht ↦ mul_nonneg ?_ (contrProd_nonneg
    (fun i ↦ linRate_mul_stepSize_le M μ hμmin0 hμmin h0 h1 i) _ _)
  have hkt : k ≤ t := (mem_Ico.1 ht).1
  exact sub_nonneg.2 (stepSize_anti h0 (Nat.le_add_left 1 k) (by omega))

/-! ## The uniform weight constant `K_β` -/

/-- `K_β = η₀ t₁ + 3η₀/(a η_{t₁+1})`, `t₁ = tdBurnIn`, `a = μmin(1−γ)`: free of `k` and `T`
(check fix F1: it depends on `a` and `η₀`, it is not universal). -/
noncomputable def linWeightConst (M : DiscountedMDP State Action) (μmin η₀ : ℝ) : ℝ :=
  η₀ * tdBurnIn M μmin η₀ + 3 * η₀ / (linRate M μmin * stepSize η₀ (tdBurnIn M μmin η₀ + 1))

theorem linWeightConst_nonneg (M : DiscountedMDP State Action) {μmin η₀ : ℝ}
    (hμmin0 : 0 < μmin) (h0 : 0 < η₀) : 0 ≤ linWeightConst M μmin η₀ := by
  have := linRate_pos M hμmin0
  have := stepSize_pos h0 (Nat.le_add_left 1 (tdBurnIn M μmin η₀))
  unfold linWeightConst; positivity

/-- The schedule facts used by the scalar lemmas. -/
theorem linStepSeq_facts (M : DiscountedMDP State Action) (μ : FiniteDistribution State)
    {μmin η₀ : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) :
    (∀ i, 0 ≤ linStepSeq η₀ i) ∧ (∀ i, linRate M μmin * linStepSeq η₀ i ≤ 1) ∧
    (∀ i, linStepSeq η₀ (i + 1) ≤ linStepSeq η₀ i) ∧ (∀ i, linStepSeq η₀ i ≤ η₀) ∧
    (∀ k, tdBurnIn M μmin η₀ ≤ k → linStepSeq η₀ k - linStepSeq η₀ (k + 1) ≤
      linRate M μmin / 2 * linStepSeq η₀ (k + 1) * linStepSeq η₀ k) := by
  refine ⟨fun i ↦ stepSize_nonneg h0.le _,
    fun i ↦ linRate_mul_stepSize_le M μ hμmin0 hμmin h0.le h1 i,
    fun i ↦ stepSize_succ_le_stepSize h0.le (Nat.le_add_left 1 i),
    fun i ↦ stepSize_le h0.le (Nat.le_add_left 1 i), fun k hk ↦ ?_⟩
  have ha0 := linRate_pos M hμmin0
  have hcube : 2 / (linRate M μmin * η₀) ≤ natCubeRoot (k + 1 + 1) := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (natCubeRoot_nonneg _) ?_
    rw [natCubeRoot_cube]
    have h3 : (2 / (linRate M μmin * η₀)) ^ 3 ≤ (tdBurnIn M μmin η₀ : ℝ) := by
      rw [tdBurnIn]
      push_cast
      have := Nat.le_ceil ((2 / (μmin * (1 - M.discount) * η₀)) ^ 3)
      unfold linRate
      linarith
    have : (tdBurnIn M μmin η₀ : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show tdBurnIn M μmin η₀ ≤ k + 1 + 1 by omega)
    linarith
  exact stepSize_sub_succ_le h0 ha0 (Nat.le_add_left 1 k) hcube

/-- `η'_k σ_k ≤ K_β` for all `k` and `T`. -/
theorem linStepSeq_mul_contrSum_le (M : DiscountedMDP State Action) (μ : FiniteDistribution State)
    {μmin η₀ : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (T k : ℕ) :
    linStepSeq η₀ k * contrSum (linRate M μmin) (linStepSeq η₀) T k ≤ linWeightConst M μmin η₀ := by
  obtain ⟨he0, hae, hanti, hE, hslow⟩ := linStepSeq_facts M μ hμmin0 hμmin h0 h1
  exact mul_contrSum_le (linRate_pos M hμmin0) he0 hae hanti hE
    (stepSize_pos h0 (Nat.le_add_left 1 _)) hslow T k

/-- **B2/F1: uniform weight bound.** `‖linWeight T k v‖_∞ ≤ K_β ‖v‖_∞` for all `k`, `T`. -/
theorem norm_linWeight_mulVec_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (T k : ℕ) (v : State → ℝ) :
    ‖linWeight M π μ η₀ T k *ᵥ v‖ ≤ linWeightConst M μmin η₀ * ‖v‖ := by
  have hb := linStepSeq_mul_contrSum_le M μ hμmin0 hμmin h0 h1 T k
  have he := stepSize_nonneg h0.le (k + 1)
  calc ‖linWeight M π μ η₀ T k *ᵥ v‖
      = stepSize η₀ (k + 1) * ‖∑ t ∈ Ico k T, linKernel M π μ η₀ (k + 1) (t + 1) *ᵥ v‖ := by
        rw [linWeight, smul_mulVec, sum_mulVec, norm_smul, Real.norm_eq_abs, abs_of_nonneg he]
    _ ≤ stepSize η₀ (k + 1) * ∑ t ∈ Ico k T,
          contrProd (linRate M μmin) (linStepSeq η₀) (k + 1) (t + 1) * ‖v‖ := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun t _ ↦ ?_)) he
        exact norm_linKernel_mulVec_le M π μ h0.le h1 hμmin0 hμmin _ _ v
    _ = linStepSeq η₀ k * contrSum (linRate M μmin) (linStepSeq η₀) T k * ‖v‖ := by
        rw [← sum_mul, contrSum, linStepSeq, mul_assoc]
    _ ≤ linWeightConst M μmin η₀ * ‖v‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg v)

/-! ## F2: the telescoping identity and the gap to `A⁻¹` -/

/-- **F2.** `A ∑_{t ∈ [k,T)} η'_{t+1} G_{k+1,t+1} = I − G_{k+1,T+1}` for `k ≤ T`. -/
theorem tdA_mul_sum_linKernel [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) {k T : ℕ}
    (hkT : k ≤ T) :
    tdA M π μ * ∑ t ∈ Ico k T, stepSize η₀ (t + 1 + 1) • linKernel M π μ η₀ (k + 1) (t + 1) =
      1 - linKernel M π μ η₀ (k + 1) (T + 1) := by
  induction T, hkT using Nat.le_induction with
  | base => simp [linKernel_self]
  | succ T hkT ih =>
    rw [sum_Ico_succ_top hkT, Matrix.mul_add, ih,
      linKernel_succ M π μ η₀ (show k + 1 ≤ T + 1 by omega), linStep, Matrix.sub_mul,
      Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul]
    abel

/-- `linWeight T k − A⁻¹ = ∑_{t∈[k,T)} (η'_k − η'_{t+1}) G_{k+1,t+1} − A⁻¹ G_{k+1,T+1}` (`k ≤ T`). -/
theorem linWeight_sub_inv_eq [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) {μmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {k T : ℕ} (hkT : k ≤ T) :
    linWeight M π μ η₀ T k - (tdA M π μ)⁻¹ =
      ∑ t ∈ Ico k T, (stepSize η₀ (k + 1) - stepSize η₀ (t + 1 + 1)) •
          linKernel M π μ η₀ (k + 1) (t + 1) -
        (tdA M π μ)⁻¹ * linKernel M π μ η₀ (k + 1) (T + 1) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)
  have hS : ∑ t ∈ Ico k T, stepSize η₀ (t + 1 + 1) • linKernel M π μ η₀ (k + 1) (t + 1) =
      (tdA M π μ)⁻¹ - (tdA M π μ)⁻¹ * linKernel M π μ η₀ (k + 1) (T + 1) := by
    have h := congrArg (fun X ↦ (tdA M π μ)⁻¹ * X) (tdA_mul_sum_linKernel M π μ η₀ hkT)
    simp only at h
    rwa [Matrix.nonsing_inv_mul_cancel_left (h := hdet), Matrix.mul_sub, Matrix.mul_one] at h
  have hW : linWeight M π μ η₀ T k = ∑ t ∈ Ico k T, (stepSize η₀ (k + 1) -
      stepSize η₀ (t + 1 + 1)) • linKernel M π μ η₀ (k + 1) (t + 1) +
      ∑ t ∈ Ico k T, stepSize η₀ (t + 1 + 1) • linKernel M π μ η₀ (k + 1) (t + 1) := by
    rw [linWeight, smul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun t _ ↦ by rw [← add_smul, sub_add_cancel]
  rw [hW, hS]
  abel

/-- `‖(linWeight T k − A⁻¹) v‖_∞ ≤ (τ_k + p_{k+1,T+1}/a) ‖v‖_∞` for `k ≤ T`. -/
theorem norm_linWeight_sub_inv_mulVec_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    {k T : ℕ} (hkT : k ≤ T) (v : State → ℝ) :
    ‖(linWeight M π μ η₀ T k - (tdA M π μ)⁻¹) *ᵥ v‖ ≤
      (contrDrift (linRate M μmin) (linStepSeq η₀) T k +
        contrProd (linRate M μmin) (linStepSeq η₀) (k + 1) (T + 1) / linRate M μmin) * ‖v‖ := by
  have ha := linRate_pos M hμmin0
  have e : (1 - M.discount) * μmin = linRate M μmin := by unfold linRate; ring
  set a := linRate M μmin
  have ha' : a ≠ 0 := ha.ne'
  set p := contrProd a (linStepSeq η₀)
  rw [linWeight_sub_inv_eq M π μ η₀ hμmin0 hμmin hkT, sub_mulVec, sum_mulVec]
  have hsum : ‖∑ t ∈ Ico k T, ((stepSize η₀ (k + 1) - stepSize η₀ (t + 1 + 1)) •
      linKernel M π μ η₀ (k + 1) (t + 1)) *ᵥ v‖ ≤
      contrDrift a (linStepSeq η₀) T k * ‖v‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [contrDrift, sum_mul]
    refine sum_le_sum fun t ht ↦ ?_
    have hkt : k ≤ t := (mem_Ico.1 ht).1
    have hd : 0 ≤ stepSize η₀ (k + 1) - stepSize η₀ (t + 1 + 1) :=
      sub_nonneg.2 (stepSize_anti h0.le (Nat.le_add_left 1 k) (by omega))
    rw [smul_mulVec, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd, linStepSeq, linStepSeq,
      mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (norm_linKernel_mulVec_le M π μ h0.le h1 hμmin0 hμmin _ _ v) hd
  have hinv : ‖((tdA M π μ)⁻¹ * linKernel M π μ η₀ (k + 1) (T + 1)) *ᵥ v‖ ≤
      p (k + 1) (T + 1) / a * ‖v‖ := by
    rw [← mulVec_mulVec]
    refine (norm_tdA_inv_mulVec_le M π μ hμmin0 hμmin _).trans ?_
    have hK := norm_linKernel_mulVec_le M π μ h0.le h1 hμmin0 hμmin (k + 1) (T + 1) v
    rw [e, div_le_iff₀ ha]
    calc _ ≤ p (k + 1) (T + 1) * ‖v‖ := hK
      _ = _ := by field_simp
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ contrDrift a (linStepSeq η₀) T k * ‖v‖ + p (k + 1) (T + 1) / a * ‖v‖ := add_le_add hsum hinv
    _ = _ := by ring

/-! ## Summed gap bound -/

theorem linStepSeq_eq {η₀ : ℝ} (k : ℕ) :
    linStepSeq η₀ k = η₀ / natCubeRoot (k + 1) ^ 2 := by
  rw [linStepSeq, stepSize_eq]

/-- `(k+1) η'_k = η₀ (k+1)^{1/3}`. -/
theorem linStepSeq_mul_succ {η₀ : ℝ} (k : ℕ) :
    linStepSeq η₀ k * ((k : ℝ) + 1) = η₀ * natCubeRoot (k + 1) := by
  have hu := natCubeRoot_pos (Nat.le_add_left 1 k)
  have hc := natCubeRoot_cube (k + 1)
  push_cast at hc
  rw [linStepSeq_eq, ← hc]
  field_simp

/-- `∑_{k<T} (τ_k + p_{k+1,T+1}/a) ≤ (3K_β² + 1/a²) u_T²/η₀` for `T ≥ 1`. -/
theorem sum_linWeightGap_le (M : DiscountedMDP State Action) (μ : FiniteDistribution State)
    {μmin η₀ : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) {T : ℕ} (hT : 1 ≤ T) :
    ∑ k ∈ range T, (contrDrift (linRate M μmin) (linStepSeq η₀) T k +
        contrProd (linRate M μmin) (linStepSeq η₀) (k + 1) (T + 1) / linRate M μmin) ≤
      (3 * linWeightConst M μmin η₀ ^ 2 + 1 / linRate M μmin ^ 2) * natCubeRoot T ^ 2 / η₀ := by
  obtain ⟨he0, hae, hanti, hE, hslow⟩ := linStepSeq_facts M μ hμmin0 hμmin h0 h1
  have ha := linRate_pos M hμmin0
  have hK0 : 0 ≤ linWeightConst M μmin η₀ := linWeightConst_nonneg M hμmin0 h0
  have hKσ : ∀ k, linStepSeq η₀ k * contrSum (linRate M μmin) (linStepSeq η₀) T k ≤
      linWeightConst M μmin η₀ :=
    fun k ↦ linStepSeq_mul_contrSum_le M μ hμmin0 hμmin h0 h1 T k
  have h0' : ∀ i, 0 ≤ linRate M μmin * linStepSeq η₀ i := fun i ↦ mul_nonneg ha.le (he0 i)
  have huT := natCubeRoot_pos hT
  set a := linRate M μmin
  set K := linWeightConst M μmin η₀
  set u := natCubeRoot T
  -- `(e_k − e_{k+1})(k+2) ≤ e_k`, i.e. `η₀ u_{k+1} ≤ η₀ u_{k+2}`
  have hd : ∀ k : ℕ, (linStepSeq η₀ k - linStepSeq η₀ (k + 1)) * ((k : ℝ) + 2) ≤
      linStepSeq η₀ k := by
    intro k
    have h1' := linStepSeq_mul_succ (η₀ := η₀) k
    have h2' := linStepSeq_mul_succ (η₀ := η₀) (k + 1)
    have hmono : natCubeRoot (k + 1) ≤ natCubeRoot (k + 1 + 1) := natCubeRoot_mono (Nat.le_succ _)
    push_cast at h2'
    nlinarith [mul_le_mul_of_nonneg_left hmono h0.le]
  have hτ : ∀ k, contrDrift a (linStepSeq η₀) T k ≤
      K / ((k : ℝ) + 2) * contrSum a (linStepSeq η₀) T k :=
    fun k ↦ contrDrift_le hae hd hK0 hKσ T k (by omega)
  -- per-`k` drift bound `τ_k ≤ K² u_T / η₀ · u_{k+1}^{-2}` for `k < T`
  have hτk : ∀ k ∈ range T, contrDrift a (linStepSeq η₀) T k ≤ K ^ 2 * u / η₀ *
      (1 / natCubeRoot (k + 1) ^ 2) := by
    intro k hk
    have hkT : k + 1 ≤ T := mem_range.1 hk
    have hek : 0 < linStepSeq η₀ k := stepSize_pos h0 (Nat.le_add_left 1 k)
    have hσ : contrSum a (linStepSeq η₀) T k ≤ K / linStepSeq η₀ k := by
      rw [le_div_iff₀ hek, mul_comm]; exact hKσ k
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hu1 := natCubeRoot_pos (Nat.le_add_left 1 k)
    have hmono : natCubeRoot (k + 1) ≤ u := natCubeRoot_mono hkT
    have h1' := linStepSeq_mul_succ (η₀ := η₀) k
    have hden : η₀ * natCubeRoot (k + 1) ≤ ((k : ℝ) + 2) * linStepSeq η₀ k := by nlinarith
    calc contrDrift a (linStepSeq η₀) T k
        ≤ K / ((k : ℝ) + 2) * (K / linStepSeq η₀ k) :=
          (hτ k).trans (mul_le_mul_of_nonneg_left hσ (div_nonneg hK0 hk2.le))
      _ = K ^ 2 / (((k : ℝ) + 2) * linStepSeq η₀ k) := by
          field_simp
      _ ≤ K ^ 2 / (η₀ * natCubeRoot (k + 1)) :=
          div_le_div_of_nonneg_left (sq_nonneg K) (by positivity) hden
      _ = K ^ 2 * natCubeRoot (k + 1) / η₀ * (1 / natCubeRoot (k + 1) ^ 2) := by
          field_simp
      _ ≤ K ^ 2 * u / η₀ * (1 / natCubeRoot (k + 1) ^ 2) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmono (sq_nonneg K)) h0.le) (by positivity)
  have hsum1 : ∑ k ∈ range T, contrDrift a (linStepSeq η₀) T k ≤ 3 * K ^ 2 * u ^ 2 / η₀ := by
    calc _ ≤ ∑ k ∈ range T, K ^ 2 * u / η₀ * (1 / natCubeRoot (k + 1) ^ 2) := sum_le_sum hτk
      _ = K ^ 2 * u / η₀ * ∑ k ∈ range T, 1 / natCubeRoot (k + 1) ^ 2 := by rw [mul_sum]
      _ ≤ K ^ 2 * u / η₀ * (3 * u) :=
          mul_le_mul_of_nonneg_left (sum_range_inv_sq_natCubeRoot_succ_le T) (by positivity)
      _ = _ := by ring
  -- the end term
  have hsum2 : ∑ k ∈ range T, contrProd a (linStepSeq η₀) (k + 1) (T + 1) / a ≤
      1 / a ^ 2 * u ^ 2 / η₀ := by
    have htel := mul_sum_contrProd_le ha.le hae hanti hT
    have hle : ∀ k ∈ range T, contrProd a (linStepSeq η₀) (k + 1) (T + 1) ≤
        contrProd a (linStepSeq η₀) (k + 1) T := by
      intro k hk
      rw [contrProd_succ_top (by simp at hk; omega)]
      have := contrProd_nonneg hae (k + 1) T
      nlinarith [h0' T]
    have heT : linStepSeq η₀ (T - 1) = η₀ / u ^ 2 := by
      rw [linStepSeq_eq, Nat.sub_add_cancel hT]
    have hpos : 0 < a * linStepSeq η₀ (T - 1) := mul_pos ha (by rw [heT]; positivity)
    have hS : ∑ k ∈ range T, contrProd a (linStepSeq η₀) (k + 1) T ≤
        1 / (a * linStepSeq η₀ (T - 1)) := by
      rw [le_div_iff₀ hpos, mul_comm]; exact htel
    have ha' : a ≠ 0 := ha.ne'
    have hu' : u ≠ 0 := huT.ne'
    have h0'' : η₀ ≠ 0 := h0.ne'
    calc ∑ k ∈ range T, contrProd a (linStepSeq η₀) (k + 1) (T + 1) / a
        = (∑ k ∈ range T, contrProd a (linStepSeq η₀) (k + 1) (T + 1)) / a := by rw [sum_div]
      _ ≤ (1 / (a * linStepSeq η₀ (T - 1))) / a :=
          div_le_div_of_nonneg_right ((sum_le_sum hle).trans hS) ha.le
      _ = _ := by rw [heT]; field_simp
  rw [sum_add_distrib]
  calc _ ≤ 3 * K ^ 2 * u ^ 2 / η₀ + 1 / a ^ 2 * u ^ 2 / η₀ := add_le_add hsum1 hsum2
    _ = _ := by ring

end StatisticalRL.Ch7Rest.TDInference

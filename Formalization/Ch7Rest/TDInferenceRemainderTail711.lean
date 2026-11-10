import Formalization.Ch7Rest.TDInferenceAzuma711
import Formalization.Ch7Rest.TDInferenceLinRemainder711

/-!
# Infrastructure toward Theorem 7.11 (not the printed result): exponential tail of the remainder `E_T`

Source: `chapters/inference.tex:52–64` (i.i.d. sampling), :72 (update), :82, :88 (`V̄_T`, `Δ̄_T`),
:104–117 (`A`), :134 (`η_t = η₀ t^{-2/3}`). Library infrastructure for the Azuma route of the
corrected-7.11 plan; no source result is claimed.

With `E_T = √TΔ̄_T − linPart` (`scaledError_sub_linPart_eq`, B3):

  `E_T(s) = remTransient(s) − ∑_{k<T} remMartInc k s`,
  `remMartInc k s = T^{-1/2} (linWeight T k ζ_k)(s)`, `ζ_k = (A_{ω k} − A)Δ_k`
  (`scaledError_sub_linPart_apply_eq_rem`).

* `remTruncInc r k s = 1{‖Δ_k‖_∞ ≤ r_k} · remMartInc k s` is a bounded martingale-difference
  sequence (`remTruncInc_isBoundedMartDiff`): the indicator depends on the coordinates `< k`,
  resampling coordinate `k` averages `ζ_k` to `0`, and `|remTruncInc| ≤ T^{-1/2} K_β 2(1+γ) r_k`.
* `sum_sq_contrProd_zero_le` (needed for the variance proxy): `∑_{k<T} p_{0,k}² ≤ 1 + K_β/η₀`.
* `pathProb_le_norm_remainder_le` (general): for `0 < δ₁, δ₂ ≤ 1` and `T ≥ 1`, with
  `r_k` the step-1 radius at `δ₁`,
  `P(T^{-1/2}K_β‖Δ_0‖/η₀ + √(2 v_T log(2/δ₂)) ≤ ‖E_T‖_∞) ≤ (T+1)|S|δ₁ + |S|δ₂`,
  `v_T = remVar = T⁻¹(2K_β(1+γ))²(2‖Δ_0‖²(1 + K_β/η₀) + 12C²K_Aη₀ log(2/δ₁) T^{1/3})`.
* `pathProb_le_norm_remainder_le_rate` (`δ₁ = T⁻³`, `δ₂ = T⁻¹`): for `T ≥ 1`,
  `P(K_R T^{-1/3} log(2T) ≤ ‖E_T‖_∞) ≤ 3|S|/T` with the `T`-free `K_R = remTailConst`.
  The rate is `T^{-1/3} log T` (one `√log` from the truncation radius, one from the second Azuma),
  not `T^{-1/3} √(log T)`.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis StatisticalRL.Probability.PathAzuma

variable {State Action : Type} [Fintype State] [Fintype Action]

/-! ## Scalar facts -/

theorem linWeightConst_pos (M : DiscountedMDP State Action) {μmin η₀ : ℝ}
    (hμmin0 : 0 < μmin) (h0 : 0 < η₀) : 0 < linWeightConst M μmin η₀ := by
  have := linRate_pos M hμmin0
  have := stepSize_pos h0 (Nat.le_add_left 1 (tdBurnIn M μmin η₀))
  have : (0 : ℝ) ≤ tdBurnIn M μmin η₀ := Nat.cast_nonneg _
  unfold linWeightConst; positivity

/-- **Transient squares are summable**: `∑_{k<T} p_{0,k}² ≤ 1 + K_β/η₀`. -/
theorem sum_sq_contrProd_zero_le (M : DiscountedMDP State Action) (μ : FiniteDistribution State)
    {μmin η₀ : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (T : ℕ) :
    ∑ k ∈ range T, contrProd (linRate M μmin) (linStepSeq η₀) 0 k ^ 2 ≤
      1 + linWeightConst M μmin η₀ / η₀ := by
  obtain ⟨he0, hae, _, _, _⟩ := linStepSeq_facts M μ hμmin0 hμmin h0 h1
  have ha := linRate_pos M hμmin0
  have h0' : ∀ i, 0 ≤ linRate M μmin * linStepSeq η₀ i := fun i ↦ mul_nonneg ha.le (he0 i)
  set p := contrProd (linRate M μmin) (linStepSeq η₀)
  have hsq : ∀ k, p 0 k ^ 2 ≤ p 0 k := fun k ↦ by
    have := contrProd_nonneg hae 0 k
    have := contrProd_le_one h0' hae 0 k
    nlinarith
  have hstep : ∀ k, p 0 (k + 1) ≤ p 1 (k + 1) := fun k ↦ by
    rw [show p 0 (k + 1) = (1 - linRate M μmin * linStepSeq η₀ 0) * p 1 (k + 1) from
      contrProd_succ_bot (Nat.succ_pos k)]
    have := contrProd_nonneg hae 1 (k + 1)
    have := h0' 0
    nlinarith
  have hK := linStepSeq_mul_contrSum_le M μ hμmin0 hμmin h0 h1 T 0
  have he0' : linStepSeq η₀ 0 = η₀ := by simp [linStepSeq, stepSize]
  rw [he0'] at hK
  have hσ : contrSum (linRate M μmin) (linStepSeq η₀) T 0 ≤ linWeightConst M μmin η₀ / η₀ := by
    rw [le_div_iff₀ h0, mul_comm]; exact hK
  have hσ' : ∑ k ∈ range T, p 1 (k + 1) = contrSum (linRate M μmin) (linStepSeq η₀) T 0 := by
    rw [contrSum, range_eq_Ico]
  calc ∑ k ∈ range T, p 0 k ^ 2
      ≤ ∑ k ∈ range T, p 0 k := sum_le_sum fun k _ ↦ hsq k
    _ ≤ ∑ k ∈ range (T + 1), p 0 k :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (Nat.le_succ T))
          fun k _ _ ↦ contrProd_nonneg hae 0 k
    _ = ∑ k ∈ range T, p 0 (k + 1) + p 0 0 := sum_range_succ' _ _
    _ ≤ ∑ k ∈ range T, p 1 (k + 1) + 1 := by
        rw [show p 0 0 = 1 from contrProd_self 0]; exact add_le_add (sum_le_sum fun k _ ↦ hstep k) le_rfl
    _ ≤ 1 + linWeightConst M μmin η₀ / η₀ := by rw [hσ']; linarith

/-! ## The martingale part of `E_T` -/

variable [DecidableEq State]

/-- `‖(A_x − A)Δ‖_∞ ≤ 2(1+γ)‖Δ‖_∞`. -/
theorem norm_linMartVec_le (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (x : Tuple State Action) (Δ : State → ℝ) :
    ‖linMartVec M π μ x Δ‖ ≤ 2 * (1 + M.discount) * ‖Δ‖ := by
  set D := ‖Δ‖
  have hγ := M.discount_nonneg
  have hD0 : 0 ≤ D := norm_nonneg Δ
  have hΔ : ∀ s', |Δ s'| ≤ D := fun s' ↦ abs_apply_le_norm Δ s'
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s' ↦ ?_
  rw [Real.norm_eq_abs]
  have hA : |sampleA M x Δ s'| ≤ (1 + M.discount) * D := by
    rw [sampleA_apply]
    split_ifs
    · calc |Δ s' - M.discount * Δ x.2.2| ≤ |Δ s'| + M.discount * |Δ x.2.2| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_of_nonneg hγ]
        _ ≤ D + M.discount * D := add_le_add (hΔ s') (mul_le_mul_of_nonneg_left (hΔ _) hγ)
        _ = (1 + M.discount) * D := by ring
    · simpa using mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + M.discount) hD0
  have hAΔ : |(tdA M π μ *ᵥ Δ) s'| ≤ (1 + M.discount) * D := by
    rw [tdA_mulVec_apply]
    have hE : |(M.policyTransition π s').expectation Δ| ≤ D :=
      (M.policyTransition π s').abs_expectation_le hΔ
    have hμ0 := μ.prob_nonneg s'
    have hμ1 := prob_le_one μ s'
    calc |μ.prob s' * (Δ s' - M.discount * (M.policyTransition π s').expectation Δ)|
        = μ.prob s' * |Δ s' - M.discount * (M.policyTransition π s').expectation Δ| := by
          rw [abs_mul, abs_of_nonneg hμ0]
      _ ≤ 1 * (D + M.discount * D) := by
          refine mul_le_mul hμ1 ?_ (abs_nonneg _) zero_le_one
          refine (abs_sub _ _).trans (add_le_add (hΔ s') ?_)
          rw [abs_mul, abs_of_nonneg hγ]
          exact mul_le_mul_of_nonneg_left hE hγ
      _ = (1 + M.discount) * D := by ring
  simp only [linMartVec, Pi.sub_apply]
  calc |sampleA M x Δ s' - (tdA M π μ *ᵥ Δ) s'|
      ≤ |sampleA M x Δ s'| + |(tdA M π μ *ᵥ Δ) s'| := abs_sub _ _
    _ ≤ (1 + M.discount) * D + (1 + M.discount) * D := add_le_add hA hAΔ
    _ = 2 * (1 + M.discount) * D := by ring

/-- Any fixed linear image of `(A_x − A)Δ` is centred under the tuple law. -/
theorem sum_tupleProb_mul_mulVec_linMartVec (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (W : Matrix State State ℝ) (Δ : State → ℝ) (s : State) :
    ∑ x, tupleProb M π μ x * (W *ᵥ linMartVec M π μ x Δ) s = 0 := by
  simp only [mulVec, dotProduct, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun u _ ↦ ?_
  have : ∑ x, tupleProb M π μ x * (W s u * linMartVec M π μ x Δ u) =
      W s u * ∑ x, tupleProb M π μ x * linMartVec M π μ x Δ u := by
    rw [mul_sum]; exact sum_congr rfl fun x _ ↦ by ring
  rw [this]
  simp only [linMartVec, Pi.sub_apply, mul_sub, sum_sub_distrib, sum_tupleProb_mul_sampleA,
    ← sum_mul, sum_tupleProb, one_mul, sub_self, mul_zero]

/-- The `k`-th martingale vector `ζ_k = (A_{ω k} − A)Δ_k` (`0` for `k ≥ T`). -/
noncomputable def remMartVec (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) (k : ℕ) : State → ℝ :=
  if h : k < T then linMartVec M π μ (ω ⟨k, h⟩) (tdError M π η₀ V₀ ω k) else 0

/-- The `k`-th martingale summand of `E_T(s)`: `T^{-1/2} (linWeight T k ζ_k)(s)`. -/
noncomputable def remMartInc (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ) (T : ℕ) (s : State) (k : ℕ)
    (ω : Fin T → Tuple State Action) : ℝ :=
  (Real.sqrt T)⁻¹ * (linWeight M π μ η₀ T k *ᵥ remMartVec M π μ η₀ V₀ ω k) s

/-- The truncated summand `1{‖Δ_k‖_∞ ≤ r_k} · remMartInc k s`. -/
noncomputable def remTruncInc (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ) (r : ℕ → ℝ) (T : ℕ) (s : State)
    (k : ℕ) (ω : Fin T → Tuple State Action) : ℝ :=
  if ‖tdError M π η₀ V₀ ω k‖ ≤ r k then remMartInc M π μ η₀ V₀ T s k ω else 0

/-- The deterministic part `T^{-1/2} (∑_{t<T} G_{0,t+1}) Δ_0` of `E_T`. -/
noncomputable def remTransient (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) : State → ℝ :=
  (Real.sqrt T)⁻¹ •
    ((∑ t ∈ range T, linKernel M π μ η₀ 0 (t + 1)) *ᵥ (V₀ - M.valueFixedPoint π))

/-- **`E_T` = transient − martingale sum** (coordinate form of B3). -/
theorem scaledError_sub_linPart_apply_eq_rem (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T) (ω : Fin T → Tuple State Action) (s : State) :
    scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s =
      remTransient M π μ η₀ V₀ T s - ∑ k ∈ range T, remMartInc M π μ η₀ V₀ T s k ω := by
  have h := congrFun (scaledError_sub_linPart_eq M π μ η₀ V₀ hT ω) s
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
  rw [h, remTransient, Pi.smul_apply, smul_eq_mul, mul_sub]
  simp only [remMartInc, ← mul_sum]
  congr 2
  rw [← Fin.sum_univ_eq_sum_range (fun k ↦
    (linWeight M π μ η₀ T k *ᵥ remMartVec M π μ η₀ V₀ ω k) s)]
  refine sum_congr rfl fun k _ ↦ ?_
  simp only [remMartVec, dif_pos k.2, Fin.eta]

theorem remMartVec_congr (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    {ω ω' : Fin T → Tuple State Action} (k : ℕ)
    (h : ∀ i : Fin T, (i : ℕ) < k + 1 → ω i = ω' i) :
    remMartVec M π μ η₀ V₀ ω k = remMartVec M π μ η₀ V₀ ω' k := by
  unfold remMartVec
  split_ifs with hk
  · rw [h ⟨k, hk⟩ (by simp), tdError_congr M π η₀ V₀ k fun i hi ↦ h i (by omega)]
  · rfl

theorem norm_remMartVec_le (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) (k : ℕ) :
    ‖remMartVec M π μ η₀ V₀ ω k‖ ≤ 2 * (1 + M.discount) * ‖tdError M π η₀ V₀ ω k‖ := by
  unfold remMartVec
  split_ifs
  · exact norm_linMartVec_le M π μ _ _
  · have := M.discount_nonneg
    simp only [norm_zero]; positivity

/-- **The truncated summands form a bounded martingale-difference sequence** with deterministic
bounds `c_k = T^{-1/2} K_β 2(1+γ) r_k`, for any nonnegative truncation radii `r`. -/
theorem remTruncInc_isBoundedMartDiff (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (V₀ : State → ℝ) {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (T : ℕ) (s : State) :
    IsBoundedMartDiff (tupleProb M π μ) (T := T) (remTruncInc M π μ η₀ V₀ r T s)
      (fun k ↦ (Real.sqrt T)⁻¹ *
        (linWeightConst M μmin η₀ * (2 * (1 + M.discount) * r k))) where
  adapted k _ ω ω' h := by
    simp only [remTruncInc, remMartInc, remMartVec_congr M π μ η₀ V₀ k h,
      tdError_congr M π η₀ V₀ k fun i hi ↦ h i (by omega)]
  centred k hk ω := by
    have hΔ : ∀ x, tdError M π η₀ V₀ (Function.update ω ⟨k, hk⟩ x) k = tdError M π η₀ V₀ ω k :=
      fun x ↦ tdError_congr M π η₀ V₀ k fun i hi ↦
        Function.update_of_ne (fun h ↦ by rw [h] at hi; simp at hi) _ _
    have hv : ∀ x, remMartVec M π μ η₀ V₀ (Function.update ω ⟨k, hk⟩ x) k =
        linMartVec M π μ x (tdError M π η₀ V₀ ω k) := by
      intro x
      simp only [remMartVec, hk, dif_pos, Function.update_self, hΔ x]
    simp only [remTruncInc, hΔ, remMartInc, hv]
    split_ifs
    · have := sum_tupleProb_mul_mulVec_linMartVec M π μ (linWeight M π μ η₀ T k)
        (tdError M π η₀ V₀ ω k) s
      calc ∑ x, tupleProb M π μ x * ((Real.sqrt T)⁻¹ *
            (linWeight M π μ η₀ T k *ᵥ linMartVec M π μ x (tdError M π η₀ V₀ ω k)) s)
          = (Real.sqrt T)⁻¹ * ∑ x, tupleProb M π μ x *
            (linWeight M π μ η₀ T k *ᵥ linMartVec M π μ x (tdError M π η₀ V₀ ω k)) s := by
            rw [mul_sum]; exact sum_congr rfl fun x _ ↦ by ring
        _ = 0 := by rw [this, mul_zero]
    · simp
  bounded k _ ω := by
    have hγ := M.discount_nonneg
    have hK := linWeightConst_pos M hμmin0 h0
    have hs : 0 ≤ (Real.sqrt T)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have hc0 : 0 ≤ (Real.sqrt T)⁻¹ *
        (linWeightConst M μmin η₀ * (2 * (1 + M.discount) * r k)) := by
      have := hr k; positivity
    unfold remTruncInc
    split_ifs with htr
    · rw [remMartInc, abs_mul, abs_of_nonneg hs]
      refine mul_le_mul_of_nonneg_left ?_ hs
      refine (abs_apply_le_norm _ s).trans ((norm_linWeight_mulVec_le M π μ h0 h1 hμmin0 hμmin
        T k _).trans (mul_le_mul_of_nonneg_left ?_ hK.le))
      exact (norm_remMartVec_le M π μ η₀ V₀ ω k).trans
        (mul_le_mul_of_nonneg_left htr (by positivity))
    · simpa using hc0

/-! ## The tail bound -/

/-- The variance proxy
`v_T = T⁻¹(2K_β(1+γ))²(2‖Δ_0‖²(1 + K_β/η₀) + 12C²K_Aη₀ log(2/δ₁) T^{1/3})`. -/
noncomputable def remVar (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (V₀ : State → ℝ) (μmin η₀ : ℝ) (T : ℕ) (δ₁ : ℝ) : ℝ :=
  (T : ℝ)⁻¹ * (2 * linWeightConst M μmin η₀ * (1 + M.discount)) ^ 2 *
    (2 * ‖V₀ - M.valueFixedPoint π‖ ^ 2 * (1 + linWeightConst M μmin η₀ / η₀) +
      12 * tdIncBound M π V₀ ^ 2 * tdAzumaConst M μmin η₀ * η₀ * Real.log (2 / δ₁) *
        natCubeRoot T)

/-- The step-1 radius `r_k = p_{0,k}‖Δ_0‖ + C√(2K_A η_{k+1} log(2/δ₁))`. -/
noncomputable def remRadius (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (V₀ : State → ℝ) (μmin η₀ δ₁ : ℝ) (k : ℕ) : ℝ :=
  contrProd (linRate M μmin) (linStepSeq η₀) 0 k * ‖V₀ - M.valueFixedPoint π‖ +
    tdIncBound M π V₀ *
      Real.sqrt (2 * tdAzumaConst M μmin η₀ * stepSize η₀ (k + 1) * Real.log (2 / δ₁))

omit [DecidableEq State] in
theorem remRadius_nonneg (M : DiscountedMDP State Action) (μ : FiniteDistribution State)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) {μmin η₀ : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (δ₁ : ℝ) (k : ℕ) :
    0 ≤ remRadius M π V₀ μmin η₀ δ₁ k := by
  obtain ⟨_, hae, _, _, _⟩ := linStepSeq_facts M μ hμmin0 hμmin h0 h1
  have := contrProd_nonneg hae 0 k
  have := (tdIncBound_pos M π V₀).le
  unfold remRadius; positivity

omit [DecidableEq State] in
/-- **Variance proxy of the truncated martingale**: `∑_{k<T} c_k² ≤ v_T`. -/
theorem sum_sq_remTrunc_bound_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (V₀ : State → ℝ) (T : ℕ) {δ₁ : ℝ} (hδ₁ : 0 < δ₁) (hδ₁1 : δ₁ ≤ 1) :
    ∑ k ∈ range T, ((Real.sqrt T)⁻¹ * (linWeightConst M μmin η₀ *
      (2 * (1 + M.discount) * remRadius M π V₀ μmin η₀ δ₁ k))) ^ 2 ≤
      remVar M π V₀ μmin η₀ T δ₁ := by
  set K := linWeightConst M μmin η₀
  set γ := M.discount
  set C := tdIncBound M π V₀
  set KA := tdAzumaConst M μmin η₀
  set L := Real.log (2 / δ₁)
  set N := ‖V₀ - M.valueFixedPoint π‖
  set p := contrProd (linRate M μmin) (linStepSeq η₀)
  have hL : 0 ≤ L := Real.log_nonneg ((le_div_iff₀ hδ₁).2 (by linarith))
  have hKA := (tdAzumaConst_pos M hμmin0 h0).le
  have hsq : ((Real.sqrt T)⁻¹) ^ 2 = (T : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hr2 : ∀ k, remRadius M π V₀ μmin η₀ δ₁ k ^ 2 ≤
      2 * N ^ 2 * p 0 k ^ 2 + 4 * C ^ 2 * KA * L * stepSize η₀ (k + 1) := by
    intro k
    have he := stepSize_nonneg h0.le (k + 1)
    have hx : 0 ≤ 2 * KA * stepSize η₀ (k + 1) * L := by positivity
    have hs := Real.sq_sqrt hx
    set q := Real.sqrt (2 * KA * stepSize η₀ (k + 1) * L)
    have : remRadius M π V₀ μmin η₀ δ₁ k = p 0 k * N + C * q := rfl
    rw [this]
    nlinarith [sq_nonneg (p 0 k * N - C * q)]
  have hsum : ∑ k ∈ range T, remRadius M π V₀ μmin η₀ δ₁ k ^ 2 ≤
      2 * N ^ 2 * (1 + K / η₀) + 12 * C ^ 2 * KA * η₀ * L * natCubeRoot T := by
    refine (sum_le_sum fun k _ ↦ hr2 k).trans ?_
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have h1' := sum_sq_contrProd_zero_le M μ hμmin0 hμmin h0 h1 T
    have h2' := sum_range_stepSize_succ_le h0.le T
    have hc : 0 ≤ 4 * C ^ 2 * KA * L := by positivity
    have := mul_le_mul_of_nonneg_left h1' (by positivity : (0 : ℝ) ≤ 2 * N ^ 2)
    have := mul_le_mul_of_nonneg_left h2' hc
    nlinarith
  have hrw : ∀ k, ((Real.sqrt T)⁻¹ * (K * (2 * (1 + γ) * remRadius M π V₀ μmin η₀ δ₁ k))) ^ 2 =
      (T : ℝ)⁻¹ * (2 * K * (1 + γ)) ^ 2 * remRadius M π V₀ μmin η₀ δ₁ k ^ 2 := by
    intro k; rw [← hsq]; ring
  simp_rw [hrw]
  rw [← mul_sum, remVar]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- **Exponential tail of the remainder `E_T` (general levels)**: for `T ≥ 1`, `0 < δ₁, δ₂ ≤ 1`,
`P(T^{-1/2}K_β‖Δ_0‖/η₀ + √(2 v_T log(2/δ₂)) ≤ ‖√TΔ̄_T − linPart‖_∞) ≤ (T+1)|S|δ₁ + |S|δ₂`. -/
theorem pathProb_le_norm_remainder_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T) {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₁1 : δ₁ ≤ 1)
    (hδ₂ : 0 < δ₂) (hδ₂1 : δ₂ ≤ 1) :
    pathProb M π μ T {ω | (Real.sqrt T)⁻¹ *
        (linWeightConst M μmin η₀ * ‖V₀ - M.valueFixedPoint π‖ / η₀) +
        Real.sqrt (2 * remVar M π V₀ μmin η₀ T δ₁ * Real.log (2 / δ₂)) ≤
      ‖scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω‖} ≤
      (T + 1) * Fintype.card State * δ₁ + Fintype.card State * δ₂ := by
  set r := remRadius M π V₀ μmin η₀ δ₁
  set v := remVar M π V₀ μmin η₀ T δ₁
  set R₀ := (Real.sqrt T)⁻¹ * (linWeightConst M μmin η₀ * ‖V₀ - M.valueFixedPoint π‖ / η₀)
  set R₁ := Real.sqrt (2 * v * Real.log (2 / δ₂))
  have hr0 : ∀ k, 0 ≤ r k := remRadius_nonneg M μ π V₀ hμmin0 hμmin h0 h1 δ₁
  have hK := linWeightConst_pos M hμmin0 h0
  have hγ := M.discount_nonneg
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hL₁ : 0 < Real.log (2 / δ₁) := Real.log_pos ((lt_div_iff₀ hδ₁).2 (by linarith))
  have hL₂ : 0 < Real.log (2 / δ₂) := Real.log_pos ((lt_div_iff₀ hδ₂).2 (by linarith))
  have hv : 0 < v := by
    have := tdIncBound_pos M π V₀
    have := tdAzumaConst_pos M hμmin0 h0
    have := natCubeRoot_pos hT
    simp only [v, remVar]
    positivity
  have hR₀ : 0 ≤ R₀ := by positivity
  have hR₁ : 0 < R₁ := Real.sqrt_pos.2 (by positivity)
  set Bad : Set (Fin T → Tuple State Action) := {ω | ∃ k ≤ T, ∃ s, r k ≤ |tdError M π η₀ V₀ ω k s|}
  set Ev : State → Set (Fin T → Tuple State Action) := fun s ↦
    {ω | R₁ ≤ |∑ k ∈ range T, remTruncInc M π μ η₀ V₀ r T s k ω|}
  set F : Option State → Set (Fin T → Tuple State Action) := fun o ↦
    match o with
    | none => Bad
    | some s => Ev s
  have hsub : {ω : Fin T → Tuple State Action | R₀ + R₁ ≤
      ‖scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω‖} ⊆ ⋃ o ∈ (univ : Finset (Option State)), F o := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, mem_univ, exists_true_left]
    by_cases hb : ω ∈ Bad
    · exact ⟨none, hb⟩
    · -- on the good event the truncation is inactive
      have hgood : ∀ k, k < T → ‖tdError M π η₀ V₀ ω k‖ ≤ r k := by
        intro k hk
        refine (pi_norm_le_iff_of_nonneg (hr0 k)).2 fun s ↦ ?_
        rw [Real.norm_eq_abs]
        by_contra hlt
        exact hb ⟨k, hk.le, s, (not_le.1 hlt).le⟩
      have htr : ∀ s, ∑ k ∈ range T, remMartInc M π μ η₀ V₀ T s k ω =
          ∑ k ∈ range T, remTruncInc M π μ η₀ V₀ r T s k ω := fun s ↦
        sum_congr rfl fun k hk ↦ by
          rw [remTruncInc, if_pos (hgood k (mem_range.1 hk))]
      -- pick the coordinate attaining the sup norm
      obtain ⟨s, hs⟩ : ∃ s, R₀ + R₁ ≤ |scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s| := by
        by_contra hne
        push_neg at hne
        have := (pi_norm_lt_iff (x := scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω)
          (by positivity : 0 < R₀ + R₁)).2 fun s ↦ by
          rw [Pi.sub_apply, Real.norm_eq_abs]; exact hne s
        linarith
      refine ⟨some s, ?_⟩
      show R₁ ≤ |∑ k ∈ range T, remTruncInc M π μ η₀ V₀ r T s k ω|
      rw [scaledError_sub_linPart_apply_eq_rem M π μ η₀ V₀ hT ω s, htr s] at hs
      have htrans : |remTransient M π μ η₀ V₀ T s| ≤ R₀ := by
        rw [remTransient, Pi.smul_apply, smul_eq_mul, abs_mul,
          abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
        exact mul_le_mul_of_nonneg_left
          (abs_linTransient_le M π μ h0 h1 hμmin0 hμmin T _ s)
          (inv_nonneg.2 (Real.sqrt_nonneg _))
      have := abs_sub (remTransient M π μ η₀ V₀ T s)
        (∑ k ∈ range T, remTruncInc M π μ η₀ V₀ r T s k ω)
      linarith
  rw [pathProb_eq_prodProb]
  refine (prodProb_mono (tupleProb_nonneg M π μ) hsub).trans
    ((prodProb_biUnion_le (tupleProb_nonneg M π μ) _ F).trans ?_)
  rw [Fintype.sum_option]
  have hbad : prodProb (tupleProb M π μ) T (F none) ≤ (T + 1) * Fintype.card State * δ₁ := by
    have := pathProb_exists_le_abs_tdError_le M π μ h0 h1 hμmin0 hμmin V₀ T hδ₁ hδ₁1
    rw [pathProb_eq_prodProb] at this
    exact this
  have hev : ∀ s, prodProb (tupleProb M π μ) T (F (some s)) ≤ δ₂ := fun s ↦
    prodProb_sqrt_le_abs_sum_le (tupleProb_nonneg M π μ) (sum_tupleProb M π μ)
      (remTruncInc_isBoundedMartDiff M π μ h0 h1 hμmin0 hμmin V₀ hr0 T s) le_rfl hv
      (sum_sq_remTrunc_bound_le M π μ h0 h1 hμmin0 hμmin V₀ T hδ₁ hδ₁1) hδ₂ hδ₂1
  have hsum : ∑ s, prodProb (tupleProb M π μ) T (F (some s)) ≤ Fintype.card State * δ₂ := by
    refine (sum_le_sum fun s _ ↦ hev s).trans (le_of_eq ?_)
    rw [sum_const, card_univ, nsmul_eq_mul]
  linarith

theorem add_one_mul_inv_cube_le {t : ℝ} (ht : 1 ≤ t) : (t + 1) * (t ^ 3)⁻¹ ≤ 2 * t⁻¹ := by
  have ht0 : 0 < t := by linarith
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) ht0]
  have := mul_nonneg (mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ 2 * t + 1))
    (by linarith : (0 : ℝ) ≤ t - 1)
  nlinarith

omit [DecidableEq State] in
/-- The `T`-free constant of the rate form:
`K_R = K_β‖Δ_0‖/(η₀ log 2) + √(2(2K_β(1+γ))²(2‖Δ_0‖²(1 + K_β/η₀)/log 2 + 36C²K_Aη₀))`. -/
noncomputable def remTailConst (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) (μmin η₀ : ℝ) : ℝ :=
  linWeightConst M μmin η₀ * ‖V₀ - M.valueFixedPoint π‖ / (η₀ * Real.log 2) +
    Real.sqrt (2 * (2 * linWeightConst M μmin η₀ * (1 + M.discount)) ^ 2 *
      (2 * ‖V₀ - M.valueFixedPoint π‖ ^ 2 * (1 + linWeightConst M μmin η₀ / η₀) / Real.log 2 +
        36 * tdIncBound M π V₀ ^ 2 * tdAzumaConst M μmin η₀ * η₀))

/-- **Exponential tail of the remainder `E_T` (rate form)**: for `0 < η₀ ≤ 1`,
`0 < μmin ≤ μ(s)`, every `V₀` and `T ≥ 1`,
`P(K_R T^{-1/3} log(2T) ≤ ‖√TΔ̄_T − linPart‖_∞) ≤ 3|S|/T`, with the `T`-free
`K_R = remTailConst` (levels `δ₁ = T⁻³` for the `Δ_k` bound, `δ₂ = T⁻¹` for the tail). -/
theorem pathProb_le_norm_remainder_le_rate (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    pathProb M π μ T {ω | remTailConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) *
        Real.log (2 * T) ≤ ‖scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω‖} ≤
      3 * Fintype.card State / T := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hδ₁ : 0 < ((T : ℝ) ^ 3)⁻¹ := by positivity
  have hδ₁1 : ((T : ℝ) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hT1)
  have hδ₂ : 0 < (T : ℝ)⁻¹ := by positivity
  have hδ₂1 : (T : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT1
  have hgen := pathProb_le_norm_remainder_le M π μ h0 h1 hμmin0 hμmin V₀ hT hδ₁ hδ₁1 hδ₂ hδ₂1
  set K := linWeightConst M μmin η₀
  set N := ‖V₀ - M.valueFixedPoint π‖
  set γ := M.discount
  set C := tdIncBound M π V₀
  set KA := tdAzumaConst M μmin η₀
  set u := natCubeRoot T
  set ℓ := Real.log (2 * T)
  set L₁ := Real.log (2 / ((T : ℝ) ^ 3)⁻¹)
  set Q := (2 * K * (1 + γ)) ^ 2
  set P := 2 * N ^ 2 * (1 + K / η₀)
  set X := P / Real.log 2 + 36 * C ^ 2 * KA * η₀
  have hK := linWeightConst_pos M hμmin0 h0
  have hγ := M.discount_nonneg
  have hKA := (tdAzumaConst_pos M hμmin0 h0).le
  have hN : 0 ≤ N := norm_nonneg _
  have hP : 0 ≤ P := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hℓ2 : Real.log 2 ≤ ℓ := Real.log_le_log two_pos (by linarith)
  have hℓ : 0 < ℓ := hlog2.trans_le hℓ2
  have hu0 : 0 < u := natCubeRoot_pos hT
  have hu3 : u ^ 3 = T := natCubeRoot_cube T
  have hu1 : 1 ≤ u := by
    by_contra h
    push_neg at h
    have : u ^ 3 < 1 := pow_lt_one₀ hu0.le h (by norm_num)
    linarith
  have hw : (T : ℝ) ^ (-(1 / 3 : ℝ)) = u⁻¹ := by rw [Real.rpow_neg hT0.le]; rfl
  have hL₁ : L₁ ≤ 3 * ℓ := by
    simp only [L₁, ℓ, div_inv_eq_mul]
    calc Real.log (2 * (T : ℝ) ^ 3) ≤ Real.log ((2 * T) ^ 3) :=
          Real.log_le_log (by positivity) (by nlinarith [pow_pos hT0 3])
      _ = 3 * Real.log (2 * T) := by rw [Real.log_pow]; push_cast; ring
  have hL₀ : 0 ≤ L₁ := Real.log_nonneg ((le_div_iff₀ hδ₁).2 (by linarith))
  have hL₂ : Real.log (2 / (T : ℝ)⁻¹) = ℓ := by rw [div_inv_eq_mul]
  have hv : remVar M π V₀ μmin η₀ T ((T : ℝ) ^ 3)⁻¹ =
      (u ^ 3)⁻¹ * Q * (P + 12 * C ^ 2 * KA * η₀ * L₁ * u) := by
    simp only [remVar]
    rw [show (T : ℝ)⁻¹ = (u ^ 3)⁻¹ by rw [hu3]]
  have hℓl : 1 ≤ ℓ / Real.log 2 := (le_div_iff₀ hlog2).2 (by linarith)
  have hkey : P + 12 * C ^ 2 * KA * η₀ * L₁ * u ≤ u * ℓ * X := by
    have hPP : P ≤ P * (u * (ℓ / Real.log 2)) :=
      le_mul_of_one_le_right hP (one_le_mul_of_one_le_of_one_le hu1 hℓl)
    have hc : 0 ≤ C ^ 2 * KA * η₀ := by positivity
    have h2 : 12 * C ^ 2 * KA * η₀ * L₁ * u ≤ 36 * C ^ 2 * KA * η₀ * ℓ * u := by
      have := mul_le_mul_of_nonneg_left hL₁ (mul_nonneg hc hu0.le)
      nlinarith
    have he : u * ℓ * X = P * (u * (ℓ / Real.log 2)) + 36 * C ^ 2 * KA * η₀ * ℓ * u := by
      simp only [X]; ring
    rw [he]; linarith
  have hX : 0 ≤ X := by positivity
  have hrad : Real.sqrt (2 * remVar M π V₀ μmin η₀ T ((T : ℝ) ^ 3)⁻¹ *
      Real.log (2 / (T : ℝ)⁻¹)) ≤ u⁻¹ * ℓ * Real.sqrt (2 * Q * X) := by
    rw [hL₂, hv]
    have hsq : 2 * ((u ^ 3)⁻¹ * Q * (P + 12 * C ^ 2 * KA * η₀ * L₁ * u)) * ℓ ≤
        (u⁻¹ * ℓ) ^ 2 * (2 * Q * X) := by
      calc 2 * ((u ^ 3)⁻¹ * Q * (P + 12 * C ^ 2 * KA * η₀ * L₁ * u)) * ℓ
          = 2 * (u ^ 3)⁻¹ * Q * ℓ * (P + 12 * C ^ 2 * KA * η₀ * L₁ * u) := by ring
        _ ≤ 2 * (u ^ 3)⁻¹ * Q * ℓ * (u * ℓ * X) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = (u⁻¹ * ℓ) ^ 2 * (2 * Q * X) := by field_simp
    calc Real.sqrt (2 * ((u ^ 3)⁻¹ * Q * (P + 12 * C ^ 2 * KA * η₀ * L₁ * u)) * ℓ)
        ≤ Real.sqrt ((u⁻¹ * ℓ) ^ 2 * (2 * Q * X)) := Real.sqrt_le_sqrt hsq
      _ = u⁻¹ * ℓ * Real.sqrt (2 * Q * X) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have htr : (Real.sqrt T)⁻¹ * (K * N / η₀) ≤ K * N / (η₀ * Real.log 2) * u⁻¹ * ℓ := by
    have hs : (Real.sqrt T)⁻¹ ≤ u⁻¹ := hw ▸ inv_sqrt_le_rpow hT
    have hKN : 0 ≤ K * N / η₀ := by positivity
    calc (Real.sqrt T)⁻¹ * (K * N / η₀) ≤ u⁻¹ * (K * N / η₀) :=
          mul_le_mul_of_nonneg_right hs hKN
      _ ≤ u⁻¹ * (K * N / η₀) * (ℓ / Real.log 2) :=
          le_mul_of_one_le_right (by positivity) hℓl
      _ = K * N / (η₀ * Real.log 2) * u⁻¹ * ℓ := by field_simp
  have hconst : remTailConst M π V₀ μmin η₀ =
      K * N / (η₀ * Real.log 2) + Real.sqrt (2 * Q * X) := rfl
  refine le_trans ?_ (hgen.trans ?_)
  · rw [pathProb_eq_prodProb, pathProb_eq_prodProb]
    refine prodProb_mono (tupleProb_nonneg M π μ) fun ω hω ↦ ?_
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hconst, hw] at hω
    have : (K * N / (η₀ * Real.log 2) + Real.sqrt (2 * Q * X)) * u⁻¹ * ℓ =
        K * N / (η₀ * Real.log 2) * u⁻¹ * ℓ + u⁻¹ * ℓ * Real.sqrt (2 * Q * X) := by ring
    linarith
  · have hS : (0 : ℝ) ≤ Fintype.card State := Nat.cast_nonneg _
    have h3 := add_one_mul_inv_cube_le hT1
    calc ((T : ℝ) + 1) * Fintype.card State * ((T : ℝ) ^ 3)⁻¹ +
          Fintype.card State * (T : ℝ)⁻¹
        = Fintype.card State * (((T : ℝ) + 1) * ((T : ℝ) ^ 3)⁻¹) +
          Fintype.card State * (T : ℝ)⁻¹ := by ring
      _ ≤ Fintype.card State * (2 * (T : ℝ)⁻¹) + Fintype.card State * (T : ℝ)⁻¹ := by
          gcongr
      _ = 3 * Fintype.card State / T := by ring

end StatisticalRL.Ch7Rest.TDInference

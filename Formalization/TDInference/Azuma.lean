import Formalization.TDInference.Kernel
import Formalization.Probability.PathAzumaBridge

/-!
# Theorem 7.11 support (M8a′, step 1 of check fix F6): high-probability bound on `Δ_k`

Source: `chapters/inference.tex:52–64` (i.i.d. sampling), :72 (update), :104–117 (`A`),
:134 (`η_t = η₀ t^{-2/3}`). Library infrastructure for the Azuma route of the corrected-7.11
plan; no source result is claimed.

Indexing as in `TDInference/Linearised.lean`: `Δ_t = tdError … t`, the tuple `ω t` drives
`Δ_t → Δ_{t+1}` with `e_t = η'_t = stepSize η₀ (t+1) = linStepSeq η₀ t`, and
`Δ_{t+1} = (I − e_t A)Δ_t − e_t (ξ_t + ζ_t)` (`tdError_succ`).

* `tdError_eq_transient_sub_sum` (variation of constants): for `k ≤ T`,
  `Δ_k = G_{0,k}Δ_0 − ∑_{j<k} e_j G_{j+1,k}(ξ_j + ζ_j)` with `ζ_j = (A_{ω j} − A)Δ_j`
  (`tdTransient`, `tdIncVec`).
* `tdMartInc k s j` is the `s`-coordinate of the `j`-th summand. `tdMartInc_isBoundedMartDiff`:
  it is a martingale-difference sequence for the natural filtration of the path, with
  deterministic pathwise bounds `c_j = e_j p_{j+1,k} C` where `p_{m,t} = ∏_{i∈[m,t)}(1 − a e_i)`,
  `a = μmin(1−γ)`, and `C = tdIncBound = B + 2(1+γ)D` (`B` the noise bound, `D = tdPathBound`).
* `sum_sq_mul_contrProd_le` (squared version of `mul_contrSum_le`):
  `∑_{j<k} (e_j p_{j+1,k})² ≤ (2/a + t₁E²/e_{t₁}) e_k`.
* `pathProb_le_abs_tdError_sub_transient_le` (Azuma, any variance proxy) and
  `pathProb_le_abs_tdError_sub_transient_le_stepSize`:
  `P(|Δ_k(s) − (G_{0,k}Δ_0)(s)| ≥ C √(2 K_A e_k log(2/δ))) ≤ δ` for `0 < δ ≤ 1`, every `k ≤ T`,
  `s`, with `K_A = tdAzumaConst = 2/a + t₁η₀²/e_{t₁}` (`t₁ = tdBurnIn`); and
  `pathProb_le_abs_tdError_le_stepSize`: the same with `|Δ_k(s)|` and the radius increased by the
  transient bound `p_{0,k} ‖Δ_0‖_∞`.
* `pathProb_exists_le_abs_tdError_le`: union bound over all `k ≤ T` and `s`.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis StatisticalRL.Probability.PathAzuma

variable {State Action : Type} [Fintype State] [Fintype Action]

/-! ## The bridge: `pathWeight` and `pathProb` are the product law of `PathAzumaBridge` -/

theorem pathWeight_eq_prodWeight (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ}
    (ω : Fin T → Tuple State Action) : pathWeight M π μ ω = prodWeight (tupleProb M π μ) ω :=
  rfl

theorem pathProb_eq_prodProb (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (T : ℕ)
    (E : Set (Fin T → Tuple State Action)) :
    pathProb M π μ T E = prodProb (tupleProb M π μ) T E :=
  rfl

/-! ## Squared contraction sums -/

section Scalar

variable {a : ℝ} {e : ℕ → ℝ}

theorem sum_sq_mul_contrProd_succ (k : ℕ) :
    ∑ j ∈ range (k + 1), (e j * contrProd a e (j + 1) (k + 1)) ^ 2 =
      (1 - a * e k) ^ 2 * ∑ j ∈ range k, (e j * contrProd a e (j + 1) k) ^ 2 + e k ^ 2 := by
  rw [sum_range_succ, contrProd_self, mul_one, mul_sum]
  congr 1
  refine sum_congr rfl fun j hj ↦ ?_
  rw [contrProd_succ_top (by have := mem_range.1 hj; omega)]
  ring

/-- **Squared weight bound**: `∑_{j<k} (e_j p_{j+1,k})² ≤ (2/a + t₁E²/e_{t₁}) e_k` for an
antitone, slowly varying schedule (the variance proxy of the Azuma bound on `Δ_k`). -/
theorem sum_sq_mul_contrProd_le (ha : 0 < a) (he0 : ∀ i, 0 ≤ e i) (h1 : ∀ i, a * e i ≤ 1)
    (hanti : ∀ i, e (i + 1) ≤ e i) {E : ℝ} (hE : ∀ i, e i ≤ E) {t₁ : ℕ} (ht₁ : 0 < e t₁)
    (hslow : ∀ k, t₁ ≤ k → e k - e (k + 1) ≤ a / 2 * e (k + 1) * e k) (k : ℕ) :
    ∑ j ∈ range k, (e j * contrProd a e (j + 1) k) ^ 2 ≤ (2 / a + t₁ * E ^ 2 / e t₁) * e k := by
  have h0 : ∀ i, 0 ≤ a * e i := fun i ↦ mul_nonneg ha.le (he0 i)
  have hantimono : Antitone e := antitone_nat_of_succ_le hanti
  have hE0 : 0 ≤ E := (he0 0).trans (hE 0)
  set B := 2 / a + t₁ * E ^ 2 / e t₁ with hB
  have hC0 : 0 ≤ t₁ * E ^ 2 / e t₁ := by positivity
  have hB2 : 2 / a ≤ B := le_add_of_nonneg_right hC0
  have hB0 : 0 ≤ B := le_trans (by positivity) hB2
  have haB : 2 ≤ a * B := by
    have := (div_le_iff₀ ha).1 hB2; linarith
  have hearly : ∀ k, k ≤ t₁ → ∑ j ∈ range k, (e j * contrProd a e (j + 1) k) ^ 2 ≤ B * e k := by
    intro k hk
    have hsum : ∑ j ∈ range k, (e j * contrProd a e (j + 1) k) ^ 2 ≤ ∑ j ∈ range k, E ^ 2 := by
      refine sum_le_sum fun j _ ↦ ?_
      have hp0 := contrProd_nonneg h1 (j + 1) k
      have hp1 := contrProd_le_one h0 h1 (j + 1) k
      have hej := he0 j
      have hEj := hE j
      have hep : e j * contrProd a e (j + 1) k ≤ E := by nlinarith
      exact pow_le_pow_left₀ (mul_nonneg hej hp0) hep 2
    rw [sum_const, card_range, nsmul_eq_mul] at hsum
    have hk' : (k : ℝ) ≤ t₁ := by exact_mod_cast hk
    have hek : e t₁ ≤ e k := hantimono hk
    calc ∑ j ∈ range k, (e j * contrProd a e (j + 1) k) ^ 2
        ≤ k * E ^ 2 := hsum
      _ ≤ t₁ * E ^ 2 := by gcongr
      _ = t₁ * E ^ 2 / e t₁ * e t₁ := by field_simp
      _ ≤ t₁ * E ^ 2 / e t₁ * e k := mul_le_mul_of_nonneg_left hek hC0
      _ ≤ B * e k := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (he0 k)
  have hlate : ∀ k, t₁ ≤ k → ∑ j ∈ range k, (e j * contrProd a e (j + 1) k) ^ 2 ≤ B * e k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hearly t₁ le_rfl
    | succ k hk ih =>
      rw [sum_sq_mul_contrProd_succ]
      set ν := ∑ j ∈ range k, (e j * contrProd a e (j + 1) k) ^ 2
      have hν0 : 0 ≤ ν := sum_nonneg fun _ _ ↦ sq_nonneg _
      have hc0 : 0 ≤ 1 - a * e k := sub_nonneg.2 (h1 k)
      have hc1 : 1 - a * e k ≤ 1 := by linarith [h0 k]
      have hsq : (1 - a * e k) ^ 2 * ν ≤ (1 - a * e k) * (B * e k) := by
        rw [sq, mul_assoc]
        exact mul_le_mul_of_nonneg_left
          ((mul_le_of_le_one_left hν0 hc1).trans ih) hc0
      have hs := hslow k hk
      have hek1 := hanti k
      have hek0 := he0 k
      have hek10 := he0 (k + 1)
      have hp1 := mul_le_mul_of_nonneg_left hs hB0
      have hp2 := mul_le_mul_of_nonneg_left hek1
        (show 0 ≤ a * B / 2 * e k by have := ha.le; positivity)
      have hp3 := mul_nonneg (sub_nonneg.2 haB) (sq_nonneg (e k))
      nlinarith
  rcases le_total k t₁ with hk | hk
  · exact hearly k hk
  · exact hlate k hk

end Scalar

/-! ## Variation of constants for `Δ_k` -/

variable [DecidableEq State]

/-- The iterate `V_t` depends only on the tuples `ω i`, `i < t`. -/
theorem tdIter_congr (M : DiscountedMDP State Action) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    {ω ω' : Fin T → Tuple State Action} (t : ℕ)
    (h : ∀ i : Fin T, (i : ℕ) < t → ω i = ω' i) : tdIter M η₀ V₀ ω t = tdIter M η₀ V₀ ω' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [tdIter]
    rw [ih fun i hi ↦ h i (by omega)]
    split_ifs with ht
    · rw [h ⟨t, ht⟩ (by simp)]
    · rfl

theorem tdError_congr (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ} {ω ω' : Fin T → Tuple State Action} (t : ℕ)
    (h : ∀ i : Fin T, (i : ℕ) < t → ω i = ω' i) :
    tdError M π η₀ V₀ ω t = tdError M π η₀ V₀ ω' t := by
  simp only [tdError, tdIter_congr M η₀ V₀ t h]

/-- The `j`-th increment vector `ξ_j + ζ_j = ξ_{ω j} + (A_{ω j} − A)Δ_j` (`0` for `j ≥ T`). -/
noncomputable def tdIncVec (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) (j : ℕ) : State → ℝ :=
  if h : j < T then
    noiseVec M π (ω ⟨j, h⟩) + linMartVec M π μ (ω ⟨j, h⟩) (tdError M π η₀ V₀ ω j)
  else 0

/-- The deterministic transient `G_{0,k} Δ_0`. -/
noncomputable def tdTransient (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (k : ℕ) : State → ℝ :=
  linKernel M π μ η₀ 0 k *ᵥ (V₀ - M.valueFixedPoint π)

/-- The `s`-coordinate of the `j`-th martingale summand of `Δ_k`:
`−e_j (G_{j+1,k}(ξ_j + ζ_j))(s)`. -/
noncomputable def tdMartInc (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ) (k : ℕ) (s : State) {T : ℕ}
    (j : ℕ) (ω : Fin T → Tuple State Action) : ℝ :=
  -(stepSize η₀ (j + 1) * (linKernel M π μ η₀ (j + 1) k *ᵥ tdIncVec M π μ η₀ V₀ ω j) s)

/-- **Variation of constants**: `Δ_k = G_{0,k}Δ_0 − ∑_{j<k} e_j G_{j+1,k}(ξ_j + ζ_j)`, `k ≤ T`. -/
theorem tdError_eq_transient_sub_sum (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ)
    {T : ℕ} (ω : Fin T → Tuple State Action) :
    ∀ k, k ≤ T → tdError M π η₀ V₀ ω k = tdTransient M π μ η₀ V₀ k -
      ∑ j ∈ range k, stepSize η₀ (j + 1) •
        (linKernel M π μ η₀ (j + 1) k *ᵥ tdIncVec M π μ η₀ V₀ ω j) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [tdTransient, linKernel_self, tdError, tdIter]
  | succ k ih =>
    intro hk
    have hkT : k < T := by omega
    have hinc : tdIncVec M π μ η₀ V₀ ω k = noiseVec M π (ω ⟨k, hkT⟩) +
        linMartVec M π μ (ω ⟨k, hkT⟩) (tdError M π η₀ V₀ ω k) := by
      simp [tdIncVec, hkT]
    have htr : tdTransient M π μ η₀ V₀ (k + 1) =
        linStep M π μ η₀ k *ᵥ tdTransient M π μ η₀ V₀ k := by
      simp only [tdTransient, linKernel_succ M π μ η₀ (Nat.zero_le k), mulVec_mulVec]
    have hsum : ∑ j ∈ range k, stepSize η₀ (j + 1) •
        (linKernel M π μ η₀ (j + 1) (k + 1) *ᵥ tdIncVec M π μ η₀ V₀ ω j) =
        linStep M π μ η₀ k *ᵥ ∑ j ∈ range k, stepSize η₀ (j + 1) •
          (linKernel M π μ η₀ (j + 1) k *ᵥ tdIncVec M π μ η₀ V₀ ω j) := by
      rw [mulVec_sum]
      refine sum_congr rfl fun j hj ↦ ?_
      rw [linKernel_succ M π μ η₀ (show j + 1 ≤ k by have := mem_range.1 hj; omega),
        mulVec_smul, mulVec_mulVec]
    have hL : linStep M π μ η₀ k *ᵥ tdError M π η₀ V₀ ω k =
        linStep M π μ η₀ k *ᵥ (tdTransient M π μ η₀ V₀ k - ∑ j ∈ range k, stepSize η₀ (j + 1) •
          (linKernel M π μ η₀ (j + 1) k *ᵥ tdIncVec M π μ η₀ V₀ ω j)) :=
      congrArg _ (ih (by omega))
    rw [tdError_succ M π μ η₀ V₀ ω hkT, sum_range_succ, linKernel_self, one_mulVec, hinc, hsum,
      htr, hL, mulVec_sub, smul_add]
    abel

/-- Coordinate form: `Δ_k(s) = (G_{0,k}Δ_0)(s) + ∑_{j<k} tdMartInc k s j`. -/
theorem tdError_apply_eq (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) {k : ℕ} (hk : k ≤ T) (s : State) :
    tdError M π η₀ V₀ ω k s =
      tdTransient M π μ η₀ V₀ k s + ∑ j ∈ range k, tdMartInc M π μ η₀ V₀ k s j ω := by
  rw [tdError_eq_transient_sub_sum M π μ η₀ V₀ ω k hk]
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tdMartInc,
    sum_neg_distrib]
  ring

/-! ## The martingale-difference structure -/

/-- The pathwise increment bound `C = B + 2(1+γ)D`. -/
noncomputable def tdIncBound (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (V₀ : State → ℝ) : ℝ :=
  tdNoiseBound M π + 2 * (1 + M.discount) * tdPathBound M π V₀

omit [DecidableEq State] in
theorem tdIncBound_pos (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (V₀ : State → ℝ) : 0 < tdIncBound M π V₀ := by
  have := tdNoiseBound_pos M π
  have := tdPathBound_nonneg M π V₀
  have := M.discount_nonneg
  unfold tdIncBound; positivity

theorem tdIncVec_congr (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    {ω ω' : Fin T → Tuple State Action} (j : ℕ)
    (h : ∀ i : Fin T, (i : ℕ) < j + 1 → ω i = ω' i) :
    tdIncVec M π μ η₀ V₀ ω j = tdIncVec M π μ η₀ V₀ ω' j := by
  unfold tdIncVec
  split_ifs with hj
  · rw [h ⟨j, hj⟩ (by simp), tdError_congr M π η₀ V₀ j fun i hi ↦ h i (by omega)]
  · rfl

theorem norm_tdIncVec_le (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {T : ℕ} (ω : Fin T → Tuple State Action) (j : ℕ) :
    ‖tdIncVec M π μ η₀ V₀ ω j‖ ≤ tdIncBound M π V₀ := by
  have hC := (tdIncBound_pos M π V₀).le
  unfold tdIncVec
  split_ifs with hj
  · set x := ω ⟨j, hj⟩
    set Δ := tdError M π η₀ V₀ ω j
    set D := tdPathBound M π V₀
    have hγ := M.discount_nonneg
    have hD0 := tdPathBound_nonneg M π V₀
    have hΔ : ∀ s', |Δ s'| ≤ D := fun s' ↦ by
      simpa [Δ, tdError] using abs_tdIter_sub_le M π h0 h1 V₀ ω j s'
    refine (pi_norm_le_iff_of_nonneg hC).2 fun s' ↦ ?_
    rw [Real.norm_eq_abs]
    have hξ : |noiseVec M π x s'| ≤ tdNoiseBound M π := by
      rw [noiseVec_apply]
      split_ifs
      · exact abs_tdNoise_le M π _
      · simpa using (tdNoiseBound_pos M π).le
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
    simp only [Pi.add_apply, linMartVec, Pi.sub_apply]
    calc |noiseVec M π x s' + (sampleA M x Δ s' - (tdA M π μ *ᵥ Δ) s')|
        ≤ |noiseVec M π x s'| + (|sampleA M x Δ s'| + |(tdA M π μ *ᵥ Δ) s'|) :=
          (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
      _ ≤ tdNoiseBound M π + ((1 + M.discount) * D + (1 + M.discount) * D) :=
          add_le_add hξ (add_le_add hA hAΔ)
      _ = tdIncBound M π V₀ := by unfold tdIncBound; ring
  · simpa using hC

/-- The increment vector is centred given the past: resampling coordinate `j` averages
`ξ_j + ζ_j` to `0` (`E ξ = 0`, `E A_x Δ = AΔ`). -/
theorem sum_tupleProb_mul_tdIncVec_update (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (ω : Fin T → Tuple State Action) {j : ℕ} (hj : j < T)
    (s' : State) :
    ∑ x, tupleProb M π μ x * tdIncVec M π μ η₀ V₀ (Function.update ω ⟨j, hj⟩ x) j s' = 0 := by
  have hΔ : ∀ x, tdError M π η₀ V₀ (Function.update ω ⟨j, hj⟩ x) j = tdError M π η₀ V₀ ω j :=
    fun x ↦ tdError_congr M π η₀ V₀ j fun i hi ↦
      Function.update_of_ne (fun h ↦ by rw [h] at hi; simp at hi) _ _
  have hv : ∀ x, tdIncVec M π μ η₀ V₀ (Function.update ω ⟨j, hj⟩ x) j s' =
      noiseVec M π x s' + (sampleA M x (tdError M π η₀ V₀ ω j) s' -
        (tdA M π μ *ᵥ tdError M π η₀ V₀ ω j) s') := by
    intro x
    simp only [tdIncVec, hj, dif_pos, Function.update_self, hΔ x, Pi.add_apply, linMartVec,
      Pi.sub_apply]
  simp_rw [hv, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← sum_mul,
    sum_tupleProb_mul_noiseVec, sum_tupleProb_mul_sampleA, sum_tupleProb, one_mul]
  ring

/-- **The Doob summands of `Δ_k(s)` form a bounded martingale-difference sequence** on the
i.i.d. path law, with deterministic bounds `c_j = e_j p_{j+1,k} C`. -/
theorem tdMartInc_isBoundedMartDiff (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (V₀ : State → ℝ) (T k : ℕ) (s : State) :
    IsBoundedMartDiff (tupleProb M π μ) (T := T) (tdMartInc M π μ η₀ V₀ k s)
      (fun j ↦ linStepSeq η₀ j * contrProd (linRate M μmin) (linStepSeq η₀) (j + 1) k *
        tdIncBound M π V₀) where
  adapted j _ ω ω' h := by
    simp only [tdMartInc, tdIncVec_congr M π μ η₀ V₀ j h]
  centred j hj ω := by
    set G := linKernel M π μ η₀ (j + 1) k
    set e := stepSize η₀ (j + 1)
    set v := fun x ↦ tdIncVec M π μ η₀ V₀ (Function.update ω ⟨j, hj⟩ x) j
    have key : ∀ (a b : ℝ) (f : State → ℝ), a * -(b * ∑ s', f s') = ∑ s', -(b * a) * f s' := by
      intro a b f; rw [← mul_sum]; ring
    have hrw : ∀ x, tupleProb M π μ x * tdMartInc M π μ η₀ V₀ k s j
        (Function.update ω ⟨j, hj⟩ x) = ∑ s', -(e * tupleProb M π μ x) * (G s s' * v x s') := by
      intro x
      simp only [tdMartInc, mulVec, dotProduct]
      exact key _ _ _
    simp_rw [hrw]
    rw [sum_comm]
    refine sum_eq_zero fun s' _ ↦ ?_
    have : ∑ x, -(e * tupleProb M π μ x) * (G s s' * v x s') =
        -(e * G s s') * ∑ x, tupleProb M π μ x * v x s' := by
      rw [mul_sum]; exact sum_congr rfl fun x _ ↦ by ring
    rw [this, sum_tupleProb_mul_tdIncVec_update M π μ η₀ V₀ ω hj s', mul_zero]
  bounded j _ ω := by
    have he := stepSize_nonneg h0 (j + 1)
    have hG := norm_linKernel_mulVec_le M π μ h0 h1 hμmin0 hμmin (j + 1) k
      (tdIncVec M π μ η₀ V₀ ω j)
    have hp := contrProd_nonneg (fun i ↦ linRate_mul_stepSize_le M μ hμmin0 hμmin h0 h1 i)
      (a := linRate M μmin) (e := linStepSeq η₀) (j + 1) k
    have hv := norm_tdIncVec_le M π μ h0 h1 V₀ ω j
    simp only [tdMartInc, abs_neg, abs_mul, abs_of_nonneg he, linStepSeq]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ he
    exact (abs_apply_le_norm _ s).trans (hG.trans (mul_le_mul_of_nonneg_left hv hp))

/-! ## Azuma tails for `Δ_k(s)` -/

/-- **Azuma for `Δ_k(s)`, any variance proxy**: for `k ≤ T`, `0 < δ ≤ 1` and any
`v ≥ C² ∑_{j<k} (e_j p_{j+1,k})²`, `v > 0`,
`P(√(2v log(2/δ)) ≤ |Δ_k(s) − (G_{0,k}Δ_0)(s)|) ≤ δ`. -/
theorem pathProb_le_abs_tdError_sub_transient_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (V₀ : State → ℝ) {T k : ℕ} (hk : k ≤ T) (s : State) {v δ : ℝ} (hv : 0 < v)
    (hvk : tdIncBound M π V₀ ^ 2 * ∑ j ∈ range k,
      (linStepSeq η₀ j * contrProd (linRate M μmin) (linStepSeq η₀) (j + 1) k) ^ 2 ≤ v)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    pathProb M π μ T {ω | Real.sqrt (2 * v * Real.log (2 / δ)) ≤
      |tdError M π η₀ V₀ ω k s - tdTransient M π μ η₀ V₀ k s|} ≤ δ := by
  have hset : {ω : Fin T → Tuple State Action | Real.sqrt (2 * v * Real.log (2 / δ)) ≤
      |tdError M π η₀ V₀ ω k s - tdTransient M π μ η₀ V₀ k s|} =
      {ω | Real.sqrt (2 * v * Real.log (2 / δ)) ≤
        |∑ j ∈ range k, tdMartInc M π μ η₀ V₀ k s j ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, tdError_apply_eq M π μ η₀ V₀ ω hk s, add_sub_cancel_left]
  rw [hset, pathProb_eq_prodProb]
  refine prodProb_sqrt_le_abs_sum_le (tupleProb_nonneg M π μ) (sum_tupleProb M π μ)
    (tdMartInc_isBoundedMartDiff M π μ h0 h1 hμmin0 hμmin V₀ T k s) hk hv ?_ hδ hδ1
  refine le_trans (le_of_eq ?_) hvk
  rw [mul_sum]
  exact sum_congr rfl fun j _ ↦ by ring

/-- The Azuma variance constant `K_A = 2/a + t₁η₀²/e_{t₁}` (`a = μmin(1−γ)`, `t₁ = tdBurnIn`). -/
noncomputable def tdAzumaConst (M : DiscountedMDP State Action) (μmin η₀ : ℝ) : ℝ :=
  2 / linRate M μmin + tdBurnIn M μmin η₀ * η₀ ^ 2 / linStepSeq η₀ (tdBurnIn M μmin η₀)

omit [DecidableEq State] in
theorem tdAzumaConst_pos (M : DiscountedMDP State Action) {μmin η₀ : ℝ} (hμmin0 : 0 < μmin)
    (h0 : 0 < η₀) : 0 < tdAzumaConst M μmin η₀ := by
  have := linRate_pos M hμmin0
  have : 0 < linStepSeq η₀ (tdBurnIn M μmin η₀) := stepSize_pos h0 (Nat.le_add_left 1 _)
  unfold tdAzumaConst; positivity

omit [DecidableEq State] in
/-- The variance proxy of `Δ_k` is `≤ K_A e_k`. -/
theorem sum_sq_linStepSeq_mul_contrProd_le (M : DiscountedMDP State Action)
    (μ : FiniteDistribution State) {μmin η₀ : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (k : ℕ) :
    ∑ j ∈ range k, (linStepSeq η₀ j * contrProd (linRate M μmin) (linStepSeq η₀) (j + 1) k) ^ 2
      ≤ tdAzumaConst M μmin η₀ * linStepSeq η₀ k := by
  obtain ⟨he0, hae, hanti, hE, hslow⟩ := linStepSeq_facts M μ hμmin0 hμmin h0 h1
  exact sum_sq_mul_contrProd_le (linRate_pos M hμmin0) he0 hae hanti hE
    (stepSize_pos h0 (Nat.le_add_left 1 _)) hslow k

/-- **High-probability bound on `Δ_k(s)` (M8a′ step 1)**: for `k ≤ T`, `0 < δ ≤ 1`,
`P(C √(2 K_A η_{k+1} log(2/δ)) ≤ |Δ_k(s) − (G_{0,k}Δ_0)(s)|) ≤ δ`, with `η_{k+1} = e_k`
the step size of the next update, `C = tdIncBound` and `K_A = tdAzumaConst`. -/
theorem pathProb_le_abs_tdError_sub_transient_le_stepSize (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (V₀ : State → ℝ) {T k : ℕ} (hk : k ≤ T) (s : State) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    pathProb M π μ T {ω | tdIncBound M π V₀ *
        Real.sqrt (2 * tdAzumaConst M μmin η₀ * stepSize η₀ (k + 1) * Real.log (2 / δ)) ≤
      |tdError M π η₀ V₀ ω k s - tdTransient M π μ η₀ V₀ k s|} ≤ δ := by
  set C := tdIncBound M π V₀
  set L := Real.log (2 / δ)
  have hC := tdIncBound_pos M π V₀
  have hK := tdAzumaConst_pos M hμmin0 h0
  have he : 0 < stepSize η₀ (k + 1) := stepSize_pos h0 (Nat.le_add_left 1 k)
  have hv : 0 < C ^ 2 * (tdAzumaConst M μmin η₀ * stepSize η₀ (k + 1)) := by positivity
  have h := pathProb_le_abs_tdError_sub_transient_le M π μ h0.le h1 hμmin0 hμmin V₀ hk s hv
    (mul_le_mul_of_nonneg_left (sum_sq_linStepSeq_mul_contrProd_le M μ hμmin0 hμmin h0 h1 k)
      (sq_nonneg C)) hδ hδ1
  have hr : Real.sqrt (2 * (C ^ 2 * (tdAzumaConst M μmin η₀ * stepSize η₀ (k + 1))) * L) =
      C * Real.sqrt (2 * tdAzumaConst M μmin η₀ * stepSize η₀ (k + 1) * L) := by
    rw [show 2 * (C ^ 2 * (tdAzumaConst M μmin η₀ * stepSize η₀ (k + 1))) * L =
      C ^ 2 * (2 * tdAzumaConst M μmin η₀ * stepSize η₀ (k + 1) * L) by ring,
      Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le]
  rwa [hr] at h

/-- The transient is bounded by `p_{0,k} ‖Δ_0‖_∞`. -/
theorem abs_tdTransient_le (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ μmin : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) (V₀ : State → ℝ) (k : ℕ) (s : State) :
    |tdTransient M π μ η₀ V₀ k s| ≤
      contrProd (linRate M μmin) (linStepSeq η₀) 0 k * ‖V₀ - M.valueFixedPoint π‖ :=
  (abs_apply_le_norm _ s).trans (norm_linKernel_mulVec_le M π μ h0 h1 hμmin0 hμmin 0 k _)

/-- **High-probability bound on `|Δ_k(s)|`**: transient plus `C √(2 K_A η_{k+1} log(2/δ))`. -/
theorem pathProb_le_abs_tdError_le_stepSize (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (V₀ : State → ℝ) {T k : ℕ} (hk : k ≤ T) (s : State) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    pathProb M π μ T {ω |
      contrProd (linRate M μmin) (linStepSeq η₀) 0 k * ‖V₀ - M.valueFixedPoint π‖ +
        tdIncBound M π V₀ *
          Real.sqrt (2 * tdAzumaConst M μmin η₀ * stepSize η₀ (k + 1) * Real.log (2 / δ)) ≤
      |tdError M π η₀ V₀ ω k s|} ≤ δ := by
  refine le_trans ?_ (pathProb_le_abs_tdError_sub_transient_le_stepSize M π μ h0 h1 hμmin0 hμmin
    V₀ hk s hδ hδ1)
  rw [pathProb_eq_prodProb, pathProb_eq_prodProb]
  refine prodProb_mono (tupleProb_nonneg M π μ) fun ω hω ↦ ?_
  simp only [Set.mem_setOf_eq] at hω ⊢
  have htr := abs_tdTransient_le M π μ h0.le h1 hμmin0 hμmin V₀ k s
  have := abs_sub_abs_le_abs_sub (tdError M π η₀ V₀ ω k s) (tdTransient M π μ η₀ V₀ k s)
  linarith

/-- **Union bound over all times and states**: with probability `≥ 1 − (T+1)|S|δ`, every
`|Δ_k(s)|`, `k ≤ T`, is below its transient plus `C √(2 K_A η_{k+1} log(2/δ))`. -/
theorem pathProb_exists_le_abs_tdError_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (V₀ : State → ℝ) (T : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    pathProb M π μ T {ω | ∃ k ≤ T, ∃ s,
      contrProd (linRate M μmin) (linStepSeq η₀) 0 k * ‖V₀ - M.valueFixedPoint π‖ +
        tdIncBound M π V₀ *
          Real.sqrt (2 * tdAzumaConst M μmin η₀ * stepSize η₀ (k + 1) * Real.log (2 / δ)) ≤
      |tdError M π η₀ V₀ ω k s|} ≤ (T + 1) * Fintype.card State * δ := by
  set E : ℕ × State → Set (Fin T → Tuple State Action) := fun q ↦ {ω |
      contrProd (linRate M μmin) (linStepSeq η₀) 0 q.1 * ‖V₀ - M.valueFixedPoint π‖ +
        tdIncBound M π V₀ *
          Real.sqrt (2 * tdAzumaConst M μmin η₀ * stepSize η₀ (q.1 + 1) * Real.log (2 / δ)) ≤
      |tdError M π η₀ V₀ ω q.1 q.2|}
  have hset : {ω : Fin T → Tuple State Action | ∃ k ≤ T, ∃ s,
      contrProd (linRate M μmin) (linStepSeq η₀) 0 k * ‖V₀ - M.valueFixedPoint π‖ +
        tdIncBound M π V₀ *
          Real.sqrt (2 * tdAzumaConst M μmin η₀ * stepSize η₀ (k + 1) * Real.log (2 / δ)) ≤
      |tdError M π η₀ V₀ ω k s|} = ⋃ q ∈ range (T + 1) ×ˢ (univ : Finset State), E q := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, mem_product, mem_range, mem_univ, and_true,
      exists_prop, Prod.exists, E]
    constructor
    · rintro ⟨k, hk, s, hs⟩; exact ⟨k, s, by omega, hs⟩
    · rintro ⟨k, s, hk, hs⟩; exact ⟨k, by omega, s, hs⟩
  rw [hset, pathProb_eq_prodProb]
  refine (prodProb_biUnion_le (tupleProb_nonneg M π μ) _ E).trans ?_
  calc ∑ q ∈ range (T + 1) ×ˢ (univ : Finset State), prodProb (tupleProb M π μ) T (E q)
      ≤ ∑ _q ∈ range (T + 1) ×ˢ (univ : Finset State), δ := by
        refine sum_le_sum fun q hq ↦ ?_
        have hq1 : q.1 ≤ T := by have := (mem_product.1 hq).1; rw [mem_range] at this; omega
        exact pathProb_le_abs_tdError_le_stepSize M π μ h0 h1 hμmin0 hμmin V₀ hq1 q.2 hδ hδ1
    _ = (T + 1) * Fintype.card State * δ := by
        rw [sum_const, card_product, card_range, card_univ, nsmul_eq_mul]; push_cast; ring

end StatisticalRL.Ch7Rest.TDInference

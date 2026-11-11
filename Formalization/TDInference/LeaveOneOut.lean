import Formalization.TDInference.ZeroNoiseDecay
import Formalization.TDInference.LinearisedCovariance

/-!
# Theorem 7.11 support (M8, H3): leave-one-out structure of the TD statistic

Source: `chapters/inference.tex:52–64` (i.i.d. sampling), :72 (update), :82, :88 (`V̄_T`, `Δ̄_T`),
:104–117 (`A`), :134 (`η_t`). Library infrastructure for the Chen–Shao step (route D-half of the
corrected-7.11 plan); no source result is claimed.

Fix a sample index `i : Fin T` and a tuple `x⋆`, and write `ω' = ω[i ↦ x⋆]` (tuple `i` replaced by
the fixed `x⋆`, so that anything computed from `ω'` is independent of `ω i`). With
`Δ_t = V_t − V^π` and `δ_t = Δ_t(ω) − Δ_t(ω')` (`looDiff`):

* `δ_t = 0` for `t ≤ i`; `δ_{i+1} = −η'_i[(A_{ω i} − A_{x⋆})Δ_i + ξ_{ω i} − ξ_{x⋆}]`
  (`looDiff_succ_self`); for `i < t < T`, `δ_{t+1} = δ_t − η'_t A_{ω t} δ_t`, the zero-noise
  recursion (`looDiff_succ_of_lt`).
* `looRemainder i x⋆ ω = (√TΔ̄_T(ω) − √TΔ̄_T(ω')) − (linPart ω − linPart ω')`, the change of the
  nonlinear remainder `E_T = √TΔ̄_T − linPart` (the deterministic transient cancels).
* `looRemainder_eq` (**exact cancellation**, CHECK-plan F6): the noise contribution
  `linWeight_i(ξ_{ω i} − ξ_{x⋆})` of tuple `i` to `√TΔ̄_T` is exactly the change of `linPart`, so
  `looRemainder = −T^{-1/2}[linWeight_i (A_{ω i} − A_{x⋆})Δ_i + ∑_{k>i} linWeight_k (A_{ω k} − A)δ_k]`.
* `sum_pathWeight_mul_sq_sum_adapted`: Pythagoras for adapted, conditionally centred path
  functionals on `Fin T → Tuple` (generic; used for the `k > i` martingale sum).
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action]

/-! ## Dependence of the iterates on the samples -/

/-- `V_t` does not depend on the tuples `ω k` with `k ≥ t`. -/
theorem tdIter_update_of_le [DecidableEq State] (M : DiscountedMDP State Action) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (ω : Fin T → Tuple State Action) (k : Fin T)
    (x : Tuple State Action) :
    ∀ {t : ℕ}, t ≤ k → tdIter M η₀ V₀ (Function.update ω k x) t = tdIter M η₀ V₀ ω t
  | 0, _ => rfl
  | t + 1, ht => by
    rw [tdIter, tdIter]
    split_ifs with h
    · have hne : (⟨t, h⟩ : Fin T) ≠ k := by
        intro he; subst he; simp at ht
      rw [tdIter_update_of_le M η₀ V₀ ω k x (by omega), Function.update_of_ne hne]
    · exact tdIter_update_of_le M η₀ V₀ ω k x (by omega)

/-- The leave-one-out difference `δ_t = V_t(ω) − V_t(ω[i ↦ x⋆])`
(`= Δ_t(ω) − Δ_t(ω[i ↦ x⋆])`). -/
noncomputable def looDiff [DecidableEq State] (M : DiscountedMDP State Action) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (i : Fin T) (xs : Tuple State Action) (t : ℕ)
    (ω : Fin T → Tuple State Action) : State → ℝ :=
  tdIter M η₀ V₀ ω t - tdIter M η₀ V₀ (Function.update ω i xs) t

/-- The change of the remainder `√TΔ̄_T − linPart` when tuple `i` is replaced by `x⋆`. -/
noncomputable def looRemainder [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (i : Fin T) (xs : Tuple State Action)
    (ω : Fin T → Tuple State Action) : State → ℝ :=
  (scaledError M π η₀ V₀ ω - scaledError M π η₀ V₀ (Function.update ω i xs)) -
    (linPart M π μ η₀ ω - linPart M π μ η₀ (Function.update ω i xs))

theorem looDiff_update_of_le [DecidableEq State] (M : DiscountedMDP State Action) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (i : Fin T) (xs : Tuple State Action)
    (ω : Fin T → Tuple State Action) (k : Fin T) (x : Tuple State Action) {t : ℕ}
    (ht : t ≤ k) : looDiff M η₀ V₀ i xs t (Function.update ω k x) = looDiff M η₀ V₀ i xs t ω := by
  unfold looDiff
  rw [tdIter_update_of_le M η₀ V₀ ω k x ht]
  by_cases hk : k = i
  · subst hk
    rw [Function.update_idem]
  · rw [Function.update_comm hk x xs ω, tdIter_update_of_le M η₀ V₀ _ k x ht]

theorem looDiff_of_le [DecidableEq State] (M : DiscountedMDP State Action) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (i : Fin T) (xs : Tuple State Action)
    (ω : Fin T → Tuple State Action) {t : ℕ} (ht : t ≤ i) : looDiff M η₀ V₀ i xs t ω = 0 := by
  rw [looDiff, tdIter_update_of_le M η₀ V₀ ω i xs ht, sub_self]

/-- After the replaced index the difference follows the zero-noise recursion. -/
theorem looDiff_succ_of_lt [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ} (i : Fin T)
    (xs : Tuple State Action) (ω : Fin T → Tuple State Action) {t : ℕ} (ht : t < T)
    (hit : (i : ℕ) < t) :
    looDiff M η₀ V₀ i xs (t + 1) ω =
      zeroNoiseStep M (stepSize η₀ (t + 1)) (looDiff M η₀ V₀ i xs t ω) (ω ⟨t, ht⟩) := by
  have hne : (⟨t, ht⟩ : Fin T) ≠ i := by
    intro he; subst he; simp at hit
  have h3 := tdStep_sub_value_eq M π (stepSize η₀ (t + 1)) (tdIter M η₀ V₀ ω t) (ω ⟨t, ht⟩)
  have h4 := tdStep_sub_value_eq M π (stepSize η₀ (t + 1))
    (tdIter M η₀ V₀ (Function.update ω i xs) t) (ω ⟨t, ht⟩)
  have e1 : tdIter M η₀ V₀ ω (t + 1) =
      tdStep M (stepSize η₀ (t + 1)) (tdIter M η₀ V₀ ω t) (ω ⟨t, ht⟩) := by
    rw [tdIter, dif_pos ht]
  have e2 : tdIter M η₀ V₀ (Function.update ω i xs) (t + 1) =
      tdStep M (stepSize η₀ (t + 1)) (tdIter M η₀ V₀ (Function.update ω i xs) t) (ω ⟨t, ht⟩) := by
    rw [tdIter, dif_pos ht, Function.update_of_ne hne]
  have e3 : looDiff M η₀ V₀ i xs (t + 1) ω =
      (tdStep M (stepSize η₀ (t + 1)) (tdIter M η₀ V₀ ω t) (ω ⟨t, ht⟩) - M.valueFixedPoint π) -
        (tdStep M (stepSize η₀ (t + 1)) (tdIter M η₀ V₀ (Function.update ω i xs) t) (ω ⟨t, ht⟩) -
          M.valueFixedPoint π) := by
    rw [looDiff, e1, e2]; abel
  rw [e3, h3, h4, zeroNoiseStep, looDiff]
  funext s
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sampleA_apply]
  split_ifs <;> ring

/-- The difference created at the replaced index:
`δ_{i+1} = −η'_i[(A_{ω i} − A_{x⋆})Δ_i + (ξ_{ω i} − ξ_{x⋆})]`. -/
theorem looDiff_succ_self [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ} (i : Fin T)
    (xs : Tuple State Action) (ω : Fin T → Tuple State Action) :
    looDiff M η₀ V₀ i xs (i + 1) ω = -(stepSize η₀ (i + 1) •
      (sampleA M (ω i) (tdError M π η₀ V₀ ω i) - sampleA M xs (tdError M π η₀ V₀ ω i) +
        (noiseVec M π (ω i) - noiseVec M π xs))) := by
  have h3 := tdStep_sub_value_eq M π (stepSize η₀ (i + 1)) (tdIter M η₀ V₀ ω i) (ω i)
  have h4 := tdStep_sub_value_eq M π (stepSize η₀ (i + 1)) (tdIter M η₀ V₀ ω i) xs
  have e1 : tdIter M η₀ V₀ ω (i + 1) =
      tdStep M (stepSize η₀ (i + 1)) (tdIter M η₀ V₀ ω i) (ω i) := by
    rw [tdIter, dif_pos i.2]
  have e2 : tdIter M η₀ V₀ (Function.update ω i xs) (i + 1) =
      tdStep M (stepSize η₀ (i + 1)) (tdIter M η₀ V₀ ω i) xs := by
    rw [tdIter, dif_pos i.2, tdIter_update_of_le M η₀ V₀ ω i xs le_rfl]
    simp
  have e3 : looDiff M η₀ V₀ i xs (i + 1) ω =
      (tdStep M (stepSize η₀ (i + 1)) (tdIter M η₀ V₀ ω i) (ω i) - M.valueFixedPoint π) -
        (tdStep M (stepSize η₀ (i + 1)) (tdIter M η₀ V₀ ω i) xs - M.valueFixedPoint π) := by
    rw [looDiff, e1, e2]; abel
  rw [e3, h3, h4, tdError]
  funext s
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-! ## The exact leave-one-out decomposition -/

/-- `∑_{t<T} δ_{t+1} = −linWeight_i[(A_{ω i} − A_{x⋆})Δ_i + ξ_{ω i} − ξ_{x⋆}]
− ∑_{k>i} linWeight_k (A_{ω k} − A)δ_k` (variation of constants for `δ`). -/
theorem sum_looDiff_eq [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (i : Fin T) (xs : Tuple State Action)
    (ω : Fin T → Tuple State Action) :
    ∑ t ∈ range T, looDiff M η₀ V₀ i xs (t + 1) ω =
      -(linWeight M π μ η₀ T i *ᵥ
        (sampleA M (ω i) (tdError M π η₀ V₀ ω i) - sampleA M xs (tdError M π η₀ V₀ ω i) +
          (noiseVec M π (ω i) - noiseVec M π xs))) -
      ∑ k : Fin T, if i < k then
        linWeight M π μ η₀ T k *ᵥ linMartVec M π μ (ω k) (looDiff M η₀ V₀ i xs k ω) else 0 := by
  set z := sampleA M (ω i) (tdError M π η₀ V₀ ω i) - sampleA M xs (tdError M π η₀ V₀ ω i) +
    (noiseVec M π (ω i) - noiseVec M π xs) with hz
  set δ : ℕ → State → ℝ := fun t ↦ looDiff M η₀ V₀ i xs t ω with hδ
  set u : ℕ → State → ℝ := fun t ↦ δ (t + 1) - linStep M π μ η₀ t *ᵥ δ t with hu
  have hx : ∀ t < T, δ (t + 1) = linStep M π μ η₀ t *ᵥ δ t + u t := fun t _ ↦ by
    simp only [hu]; abel
  have h := sum_linRec_eq (linStep M π μ η₀) δ u hx
  have hδ0 : δ 0 = 0 := looDiff_of_le M η₀ V₀ i xs ω (Nat.zero_le _)
  have hsum : ∑ t ∈ range T, looDiff M η₀ V₀ i xs (t + 1) ω = ∑ t ∈ range T, δ (t + 1) := rfl
  rw [hsum, h, hδ0, mulVec_zero, zero_add,
    ← Fin.sum_univ_eq_sum_range (fun k ↦
      (∑ t ∈ Ico k T, matProd (linStep M π μ η₀) (k + 1) (t + 1)) *ᵥ u k)]
  have hW : ∀ (k : ℕ) (v : State → ℝ),
      (∑ t ∈ Ico k T, matProd (linStep M π μ η₀) (k + 1) (t + 1)) *ᵥ
        (-(stepSize η₀ (k + 1) • v)) = -(linWeight M π μ η₀ T k *ᵥ v) := by
    intro k v
    simp only [linWeight, linKernel, mulVec_neg, smul_mulVec, mulVec_smul]
  have hk : ∀ k : Fin T,
      (∑ t ∈ Ico (k : ℕ) T, matProd (linStep M π μ η₀) (k + 1) (t + 1)) *ᵥ u k =
        (if k = i then -(linWeight M π μ η₀ T i *ᵥ z) else 0) -
          (if i < k then linWeight M π μ η₀ T k *ᵥ linMartVec M π μ (ω k) (δ k) else 0) := by
    intro k
    rcases lt_trichotomy (k : ℕ) i with hlt | heq | hgt
    · have h1 : u k = 0 := by
        simp only [hu, hδ, looDiff_of_le M η₀ V₀ i xs ω hlt.le,
          looDiff_of_le M η₀ V₀ i xs ω (Nat.succ_le_of_lt hlt), mulVec_zero, sub_zero]
      have hne : k ≠ i := fun he ↦ by rw [he] at hlt; exact lt_irrefl _ hlt
      have hnlt : ¬ i < k := fun h' ↦ absurd (Fin.lt_def.1 h') (by omega)
      rw [h1, mulVec_zero, if_neg hne, if_neg hnlt, sub_zero]
    · obtain rfl : k = i := Fin.ext heq
      have h1 : u k = -(stepSize η₀ (k + 1) • z) := by
        simp only [hu, hδ, looDiff_of_le M η₀ V₀ k xs ω le_rfl, mulVec_zero, sub_zero]
        rw [looDiff_succ_self M π η₀ V₀ k xs ω]
      rw [h1, hW, if_pos rfl, if_neg (lt_irrefl _), sub_zero]
    · have hne : k ≠ i := fun he ↦ by rw [he] at hgt; exact lt_irrefl _ hgt
      have hlt' : i < k := Fin.lt_def.2 hgt
      have h1 : u k = -(stepSize η₀ (k + 1) • linMartVec M π μ (ω k) (δ k)) := by
        simp only [hu, hδ]
        rw [looDiff_succ_of_lt M π η₀ V₀ i xs ω k.2 hgt]
        simp only [Fin.eta, zeroNoiseStep, linStep, linMartVec, sub_mulVec, one_mulVec,
          smul_mulVec, smul_sub]
        abel
      rw [h1, hW, if_neg hne, if_pos hlt', zero_sub]
  rw [sum_congr rfl fun k _ ↦ hk k, sum_sub_distrib, sum_ite_eq' univ i, if_pos (mem_univ i)]

/-- **Exact leave-one-out cancellation** (CHECK-plan F6). Replacing tuple `i` by `x⋆` changes the
remainder `√TΔ̄_T − linPart` by
`−T^{-1/2}[linWeight_i (A_{ω i} − A_{x⋆})Δ_i + ∑_{k>i} linWeight_k (A_{ω k} − A)δ_k]`:
the noise term `linWeight_i(ξ_{ω i} − ξ_{x⋆})` cancels exactly against the change of `linPart`. -/
theorem looRemainder_eq [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (i : Fin T) (xs : Tuple State Action)
    (ω : Fin T → Tuple State Action) :
    looRemainder M π μ η₀ V₀ i xs ω = -((Real.sqrt T)⁻¹ •
      (linWeight M π μ η₀ T i *ᵥ
          (sampleA M (ω i) (tdError M π η₀ V₀ ω i) - sampleA M xs (tdError M π η₀ V₀ ω i)) +
        ∑ k : Fin T, if i < k then
          linWeight M π μ η₀ T k *ᵥ linMartVec M π μ (ω k) (looDiff M η₀ V₀ i xs k ω) else 0)) := by
  have hT : 1 ≤ T := by have := i.2; omega
  have hX : scaledError M π η₀ V₀ ω - scaledError M π η₀ V₀ (Function.update ω i xs) =
      (Real.sqrt T)⁻¹ • ∑ t ∈ range T, looDiff M η₀ V₀ i xs (t + 1) ω := by
    rw [scaledError_eq M π η₀ V₀ hT, scaledError_eq M π η₀ V₀ hT, ← smul_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun t _ ↦ ?_
    simp only [tdError, looDiff]
    abel
  have hL : linPart M π μ η₀ ω - linPart M π μ η₀ (Function.update ω i xs) =
      linSummand M π μ η₀ T i (ω i) - linSummand M π μ η₀ T i xs := by
    rw [linPart_eq_sum, linPart_eq_sum, ← sum_sub_distrib, sum_eq_single i]
    · rw [Function.update_self]
    · intro k _ hki
      rw [Function.update_of_ne hki, sub_self]
    · intro h; exact absurd (mem_univ i) h
  rw [looRemainder, hX, hL, sum_looDiff_eq]
  simp only [linSummand, mulVec_add, mulVec_sub, smul_add, smul_sub, smul_neg]
  abel

/-! ## Orthogonality of adapted, conditionally centred path functionals -/

/-- **Pythagoras on the path law.** If `f_j` does not depend on `ω k` for `j < k`, and each `f_k`
is centred in its own coordinate (`∑ₓ p(x) f_k(ω[k ↦ x]) = 0`), then
`E(∑_k f_k)² = ∑_k E f_k²`. -/
theorem sum_pathWeight_mul_sq_sum_adapted (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ}
    (f : Fin T → (Fin T → Tuple State Action) → ℝ)
    (hind : ∀ j k : Fin T, j < k → ∀ ω x, f j (Function.update ω k x) = f j ω)
    (hcent : ∀ k ω, ∑ x, tupleProb M π μ x * f k (Function.update ω k x) = 0) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (∑ k, f k ω) ^ 2 =
      ∑ k, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * f k ω ^ 2 := by
  have hcross : ∀ j k : Fin T, j < k →
      ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (f j ω * f k ω) = 0 := by
    intro j k hjk
    rw [sum_pathWeight_mul_eq_sum_update M π μ k (fun ω ↦ f j ω * f k ω)]
    refine sum_eq_zero fun ω _ ↦ ?_
    simp_rw [hind j k hjk]
    simp_rw [mul_left_comm (tupleProb M π μ _) (f j ω), ← mul_sum, hcent k ω, mul_zero]
  have hcross' : ∀ j k : Fin T, j ≠ k →
      ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (f j ω * f k ω) = 0 := by
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact hcross j k h
    · simp_rw [mul_comm (f j _) (f k _)]
      exact hcross k j h
  calc ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (∑ k, f k ω) ^ 2
      = ∑ j, ∑ k, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (f j ω * f k ω) := by
        simp_rw [sq, sum_mul_sum, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun j _ ↦ ?_
        rw [sum_comm]
    _ = ∑ j, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (f j ω * f j ω) := by
        refine sum_congr rfl fun j _ ↦ ?_
        rw [sum_eq_single j (fun k _ hkj ↦ hcross' j k (Ne.symm hkj))
          (fun h ↦ absurd (mem_univ j) h)]
    _ = _ := by simp_rw [sq]

end StatisticalRL.Ch7Rest.TDInference

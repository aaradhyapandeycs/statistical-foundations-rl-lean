import Formalization.TDInference.Kernel
import Formalization.TDInference.LinearisationRemainder

/-!
# Theorem 7.11 support (M5, B5 and F3): covariance of the linearised process

Source: `chapters/inference.tex:104–117` (`Λ⋆ = A⁻¹ΓA⁻ᵀ`), with `Γ := Γ_true` (SOURCE-ISSUES C43).
Library infrastructure only; no source result is claimed.

* `sum_pathWeight_mul_sum_mul_sum`: for centred per-sample functions `f_k`, `g_k` of the tuple
  only, `E[(∑_k f_k(ω k))(∑_k g_k(ω k))] = ∑_k E_x[f_k(x) g_k(x)]` under the i.i.d. path law.
* `sum_pathWeight_linPart` and `sum_pathWeight_linPart_mul_linPart` (F3): `linPart` is centred and
  `E[linPart(s) linPart(s')] = linCov T (s,s')` exactly, for every `T` and `η₀`.
* `abs_linCov_sub_le` (B5): for `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, `T ≥ 1`,
  `|Λ_T(s,s') − (A⁻¹ diag(Γ_true) A⁻ᵀ)(s,s')| ≤ K_Λ T^{-1/3}` with the `T`-free
  `K_Λ = ‖Γ_true‖_∞ (K_β + 1/a)(3K_β² + 1/a²)/η₀` (`linCovConst`), `a = μmin(1−γ)`. No sign of
  `Λ_T − Λ` is claimed (it varies), no `Γ ≻ 0` and no stationarity hypothesis.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action]

/-! ## Independent sums on the path law -/

/-- Covariance of independent centred sums on the i.i.d. path law. -/
theorem sum_pathWeight_mul_sum_mul_sum (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (f g : ℕ → Tuple State Action → ℝ) (hf : ∀ k, ∑ x, tupleProb M π μ x * f k x = 0)
    (hg : ∀ k, ∑ x, tupleProb M π μ x * g k x = 0) (T : ℕ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        ((∑ k : Fin T, f k (ω k)) * (∑ k : Fin T, g k (ω k))) =
      ∑ k ∈ range T, ∑ x, tupleProb M π μ x * (f k x * g k x) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Fintype.sum_fin_succ_snoc, sum_range_succ, ← ih]
    have hstep : ∀ ω : Fin T → Tuple State Action,
        ∑ x, pathWeight M π μ (Fin.snoc ω x : Fin (T + 1) → Tuple State Action) *
          ((∑ k : Fin (T + 1), f k ((Fin.snoc ω x : Fin (T + 1) → Tuple State Action) k)) *
            (∑ k : Fin (T + 1), g k ((Fin.snoc ω x : Fin (T + 1) → Tuple State Action) k))) =
        pathWeight M π μ ω * ((∑ k : Fin T, f k (ω k)) * (∑ k : Fin T, g k (ω k))) +
          pathWeight M π μ ω * ∑ x, tupleProb M π μ x * (f T x * g T x) := by
      intro ω
      simp only [pathWeight_snoc, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        Fin.val_castSucc, Fin.val_last]
      set F := ∑ k : Fin T, f k (ω k)
      set G := ∑ k : Fin T, g k (ω k)
      set P := pathWeight M π μ ω
      have e : ∀ x, P * tupleProb M π μ x * ((F + f T x) * (G + g T x)) =
          P * (F * G) * tupleProb M π μ x + P * F * (tupleProb M π μ x * g T x) +
            P * G * (tupleProb M π μ x * f T x) + P * (tupleProb M π μ x * (f T x * g T x)) :=
        fun x ↦ by ring
      simp_rw [e, sum_add_distrib, ← mul_sum, sum_tupleProb, hf, hg]
      ring
    simp_rw [hstep, sum_add_distrib, ← sum_mul, sum_pathWeight, one_mul]

/-- Bilinear noise identity: `E_x[(∑_u c_u ξ_x(u))(∑_u d_u ξ_x(u))] = ∑_u c_u d_u Γ_true(u)`. -/
theorem sum_tupleProb_mul_sum_noiseVec_mul [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (c d : State → ℝ) :
    ∑ x, tupleProb M π μ x * ((∑ u, c u * noiseVec M π x u) * (∑ u, d u * noiseVec M π x u)) =
      ∑ u, c u * d u * trueGamma M π μ u := by
  have e : ∀ x : Tuple State Action, tupleProb M π μ x *
      ((∑ u, c u * noiseVec M π x u) * (∑ u, d u * noiseVec M π x u)) =
      ∑ u, ∑ v, c u * d v * (tupleProb M π μ x * (noiseVec M π x u * noiseVec M π x v)) := by
    intro x
    rw [sum_mul_sum, mul_sum]
    exact sum_congr rfl fun u _ ↦ by rw [mul_sum]; exact sum_congr rfl fun v _ ↦ by ring
  simp_rw [e]
  rw [sum_comm]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [sum_comm]
  simp_rw [← mul_sum, sum_tupleProb_mul_noiseVec_mul, mul_ite, mul_zero]
  rw [sum_ite_eq]
  simp only [mem_univ, if_true]

theorem linSummand_apply [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T k : ℕ)
    (x : Tuple State Action) (s : State) :
    linSummand M π μ η₀ T k x s =
      -((Real.sqrt T)⁻¹ * ∑ u, linWeight M π μ η₀ T k s u * noiseVec M π x u) := by
  simp [linSummand, mulVec, dotProduct]

theorem sum_tupleProb_mul_linSummand [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T k : ℕ)
    (s : State) : ∑ x, tupleProb M π μ x * linSummand M π μ η₀ T k x s = 0 := by
  simp_rw [linSummand_apply, mul_neg, sum_neg_distrib, mul_sum]
  rw [sum_comm]
  simp_rw [show ∀ (u : State) (x : Tuple State Action), tupleProb M π μ x *
      ((Real.sqrt T)⁻¹ * (linWeight M π μ η₀ T k s u * noiseVec M π x u)) =
      (Real.sqrt T)⁻¹ * linWeight M π μ η₀ T k s u * (tupleProb M π μ x * noiseVec M π x u) from
    fun u x ↦ by ring]
  simp_rw [← mul_sum, sum_tupleProb_mul_noiseVec, mul_zero, sum_const_zero, neg_zero]

/-- Means of sums on the path law: `E ∑_k f_k(ω k) = ∑_k E_x f_k(x)`. -/
theorem sum_pathWeight_mul_sum (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (f : ℕ → Tuple State Action → ℝ) (T : ℕ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * ∑ k : Fin T, f k (ω k) =
      ∑ k ∈ range T, ∑ x, tupleProb M π μ x * f k x := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Fintype.sum_fin_succ_snoc, sum_range_succ, ← ih]
    have hstep : ∀ ω : Fin T → Tuple State Action,
        ∑ x, pathWeight M π μ (Fin.snoc ω x : Fin (T + 1) → Tuple State Action) *
          ∑ k : Fin (T + 1), f k ((Fin.snoc ω x : Fin (T + 1) → Tuple State Action) k) =
        pathWeight M π μ ω * ∑ k : Fin T, f k (ω k) +
          pathWeight M π μ ω * ∑ x, tupleProb M π μ x * f T x := by
      intro ω
      simp only [pathWeight_snoc, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        Fin.val_castSucc, Fin.val_last]
      have e : ∀ x, pathWeight M π μ ω * tupleProb M π μ x * ((∑ k : Fin T, f k (ω k)) + f T x) =
          pathWeight M π μ ω * (∑ k : Fin T, f k (ω k)) * tupleProb M π μ x +
            pathWeight M π μ ω * (tupleProb M π μ x * f T x) := fun x ↦ by ring
      simp_rw [e, sum_add_distrib, ← mul_sum, sum_tupleProb, mul_one]
    simp_rw [hstep, sum_add_distrib, ← sum_mul, sum_pathWeight, one_mul]

/-- `linPart` is centred: `E linPart(s) = 0`. -/
theorem sum_pathWeight_linPart [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T : ℕ)
    (s : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * linPart M π μ η₀ ω s = 0 := by
  simp_rw [linPart_eq_sum, Finset.sum_apply]
  rw [sum_pathWeight_mul_sum M π μ (fun k x ↦ linSummand M π μ η₀ T k x s) T]
  exact sum_eq_zero fun k _ ↦ sum_tupleProb_mul_linSummand M π μ η₀ T k s

/-- **F3: the exact covariance of the linearised process.**
`E[linPart(s) linPart(s')] = linCov T (s,s')` for every `T`, `η₀` and state pair. -/
theorem sum_pathWeight_linPart_mul_linPart [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T : ℕ)
    (s s' : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (linPart M π μ η₀ ω s * linPart M π μ η₀ ω s') = linCov M π μ η₀ T s s' := by
  simp_rw [linPart_eq_sum, Finset.sum_apply]
  rw [sum_pathWeight_mul_sum_mul_sum M π μ (fun k x ↦ linSummand M π μ η₀ T k x s)
    (fun k x ↦ linSummand M π μ η₀ T k x s') (fun k ↦ sum_tupleProb_mul_linSummand M π μ η₀ T k s)
    (fun k ↦ sum_tupleProb_mul_linSummand M π μ η₀ T k s') T]
  rw [linCov, smul_apply, Matrix.sum_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  have hT : (Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ = (T : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have h := sum_tupleProb_mul_sum_noiseVec_mul M π μ (fun u ↦ linWeight M π μ η₀ T k s u)
    (fun u ↦ linWeight M π μ η₀ T k s' u)
  simp_rw [linSummand_apply]
  have e : ∀ x : Tuple State Action, tupleProb M π μ x *
      (-((Real.sqrt T)⁻¹ * ∑ u, linWeight M π μ η₀ T k s u * noiseVec M π x u) *
        -((Real.sqrt T)⁻¹ * ∑ u, linWeight M π μ η₀ T k s' u * noiseVec M π x u)) =
      (T : ℝ)⁻¹ * (tupleProb M π μ x * ((∑ u, linWeight M π μ η₀ T k s u * noiseVec M π x u) *
        (∑ u, linWeight M π μ η₀ T k s' u * noiseVec M π x u))) := by
    intro x; rw [← hT]; ring
  simp_rw [e]
  rw [← mul_sum, h, mul_diagonal_mul_transpose_apply]
  congr 1
  exact sum_congr rfl fun u _ ↦ by ring

/-! ## B5: the covariance error -/

/-- `K_Λ = ‖Γ_true‖_∞ (K_β + 1/a)(3K_β² + 1/a²)/η₀`, `a = μmin(1−γ)`. -/
noncomputable def linCovConst (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (μmin η₀ : ℝ) : ℝ :=
  ‖trueGamma M π μ‖ * (linWeightConst M μmin η₀ + 1 / linRate M μmin) *
    (3 * linWeightConst M μmin η₀ ^ 2 + 1 / linRate M μmin ^ 2) / η₀

/-- **B5: the covariance of the linearised process converges at rate `T^{-1/3}`.** For
`0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)` for all `s`, `T ≥ 1` and all `s, s'`,
`|Λ_T(s,s') − (A⁻¹ diag(Γ_true) A⁻ᵀ)(s,s')| ≤ K_Λ T^{-1/3}` with the `T`-free
`K_Λ = linCovConst`. -/
theorem abs_linCov_sub_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ}
    (hT : 1 ≤ T) (s s' : State) :
    |linCov M π μ η₀ T s s' -
        ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * ((tdA M π μ)⁻¹)ᵀ) s s'| ≤
      linCovConst M π μ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have ha := linRate_pos M hμmin0
  set a := linRate M μmin
  set K := linWeightConst M μmin η₀
  set G := ‖trueGamma M π μ‖
  set V := (tdA M π μ)⁻¹
  set Γ := trueGamma M π μ
  set e : ℕ → ℝ := fun k ↦ contrDrift a (linStepSeq η₀) T k +
    contrProd a (linStepSeq η₀) (k + 1) (T + 1) / a with he
  have hK0 : 0 ≤ K := linWeightConst_nonneg M hμmin0 h0
  have hG0 : 0 ≤ G := norm_nonneg _
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hΓ : ∀ u, |Γ u| ≤ G := fun u ↦ by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm Γ u
  have hVnorm : ∀ v : State → ℝ, ‖V *ᵥ v‖ ≤ 1 / a * ‖v‖ := by
    intro v
    have h := norm_tdA_inv_mulVec_le M π μ hμmin0 hμmin v
    have e1 : (1 - M.discount) * μmin = a := by simp only [a, linRate]; ring
    rw [e1] at h
    calc ‖V *ᵥ v‖ ≤ ‖v‖ / a := h
      _ = 1 / a * ‖v‖ := by ring
  have hV : ∀ u, |V s u| ≤ 1 / a :=
    abs_apply_le_of_norm_mulVec_le V (by positivity) hVnorm s
  have hk : ∀ k ∈ range T, |(linWeight M π μ η₀ T k * diagonal Γ * (linWeight M π μ η₀ T k)ᵀ) s s' -
      (V * diagonal Γ * Vᵀ) s s'| ≤ G * (K + 1 / a) * e k := by
    intro k hkT
    have hkT' : k ≤ T := (mem_range.1 hkT).le
    have he0 : 0 ≤ e k :=
      add_nonneg (contrDrift_linStepSeq_nonneg (M := M) h0.le hμmin0 hμmin h1 T k)
        (div_nonneg (contrProd_nonneg (fun i ↦ (linStepSeq_facts M μ hμmin0 hμmin h0 h1).2.1 i)
          _ _) ha.le)
    have hrow : ∀ r, ∑ u, |(linWeight M π μ η₀ T k - V) r u| ≤ e k :=
      sum_abs_le_of_norm_mulVec_le _ he0
        (norm_linWeight_sub_inv_mulVec_le M π μ h0 h1 hμmin0 hμmin hkT')
    have hW : ∀ u, |linWeight M π μ η₀ T k s' u| ≤ K :=
      abs_apply_le_of_norm_mulVec_le _ hK0 (norm_linWeight_mulVec_le M π μ h0 h1 hμmin0 hμmin T k) s'
    exact abs_mul_diagonal_mul_transpose_sub_le _ _ Γ s s' hG0 hΓ hW hV (hrow s) (hrow s')
  have hΛ : (V * diagonal Γ * Vᵀ) s s' =
      (T : ℝ)⁻¹ * ∑ _k ∈ range T, (V * diagonal Γ * Vᵀ) s s' := by
    rw [sum_const, card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hT0.ne', one_mul]
  have hL : linCov M π μ η₀ T s s' = (T : ℝ)⁻¹ * ∑ k ∈ range T,
      (linWeight M π μ η₀ T k * diagonal Γ * (linWeight M π μ η₀ T k)ᵀ) s s' := by
    rw [linCov, smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [hL, hΛ, ← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_nonneg (inv_nonneg.2 hT0.le)]
  have hsum := sum_linWeightGap_le M μ hμmin0 hμmin h0 h1 hT
  have hc : 0 ≤ G * (K + 1 / a) := by positivity
  calc (T : ℝ)⁻¹ * |∑ k ∈ range T, ((linWeight M π μ η₀ T k * diagonal Γ *
        (linWeight M π μ η₀ T k)ᵀ) s s' - (V * diagonal Γ * Vᵀ) s s')|
      ≤ (T : ℝ)⁻¹ * ∑ k ∈ range T, G * (K + 1 / a) * e k := by
        refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hk)) ?_
        positivity
    _ = (T : ℝ)⁻¹ * (G * (K + 1 / a) * ∑ k ∈ range T, e k) := by rw [← mul_sum]
    _ ≤ (T : ℝ)⁻¹ * (G * (K + 1 / a) *
          ((3 * K ^ 2 + 1 / a ^ 2) * natCubeRoot T ^ 2 / η₀)) := by
        gcongr
    _ = linCovConst M π μ μmin η₀ * (natCubeRoot T ^ 2 / T) := by
        unfold linCovConst; ring
    _ = linCovConst M π μ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by rw [natCubeRoot_sq_div hT]

end StatisticalRL.Ch7Rest.TDInference

import Formalization.TDInference.ConvexSets.Reservoir
import Formalization.TDInference.HalfSpace
import Formalization.Probability.ConvexLindebergReservoir
import Formalization.Probability.GaussianConvexCompare

/-!
# Partial result toward Theorem 7.11 (not the printed result): the linearised statistic over all convex sets at `T^{-1/4}`

Infrastructure for the all-convex-sets route to `thm:Berry-Esseen-linear`
(`chapters/inference.tex:132–141`; `d_cvx` at :124–127; `Λ⋆ = A⁻¹ΓA⁻ᵀ` at :104–117, with
`Γ := Γ_true`, SOURCE-ISSUES C43). **No source result is claimed here.** The printed theorem is about
the full statistic `√T Δ̄_T` at rate `T^{-1/3}`; this module concerns only the linearised statistic
`linPart` (`X^lin_T = T^{-1/2} ∑_k linSummand_k`), at the weaker rate `T^{-1/4}`, with an
instance constant. It feeds the all-convex `T^{-2/9}` bound on the full statistic in
`TDInference/ConvexSets/AllConvexRate.lean`.

Route:
* the generic reservoir Lindeberg bound (pass 1, `abs_pexp_convex_sub_twinLaw_le_quarter`) applied
  to the summands `linSummand T k` with covariance factors `linFactor T k`, under the TD reservoir
  condition `exists_linFactor_reservoirCond_of_pos` (for `T ≥ linReservoirBurnIn`); this compares
  `linPart` with `N(0, Λ_T)`, `Λ_T = linCov T`, at `T^{-1/4}`;
* the Gaussian–Gaussian convex comparison `abs_real_convex_gaussian_sub_le` between `N(0, Λ_T)` and
  the target `N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)` (`gaussCov`), linear in `entryMax (Λ_T − Λ)`, which is
  `O(T^{-1/3})` by `abs_linCov_sub_le`; the lower covariance bounds come from the reservoir
  condition (for `Λ_T`) and `mul_sq_sum_abs_le_quadForm` (for `Λ`);
* small `T < linReservoirBurnIn` are absorbed in the constant (`|P − N| ≤ 1`).

Main export: `abs_linLaw_convex_sub_gaussCov_le_quarter`.
-/

open Finset Matrix MeasureTheory Metric
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-! ## Elementary bounds -/


/-- **Summand bound.** `‖linSummand T k x‖ ≤ K_β · B_ξ / √T`, with `K_β = linWeightConst` and
`B_ξ = tdNoiseBound`. -/
theorem norm_linSummand_le (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ μmin : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) (T k : ℕ) (x : Tuple State Action) :
    ‖linSummand M π μ η₀ T k x‖ ≤
      linWeightConst M μmin η₀ * tdNoiseBound M π / Real.sqrt T := by
  rw [linSummand, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hW := norm_linWeight_mulVec_le M π μ h0 h1 hμmin0 hμmin T k (noiseVec M π x)
  have hN := norm_noiseVec_le M π x
  have hK := linWeightConst_nonneg M hμmin0 h0
  calc (Real.sqrt T)⁻¹ * ‖linWeight M π μ η₀ T k *ᵥ noiseVec M π x‖
      ≤ (Real.sqrt T)⁻¹ * (linWeightConst M μmin η₀ * tdNoiseBound M π) :=
        mul_le_mul_of_nonneg_left (hW.trans (mul_le_mul_of_nonneg_left hN hK))
          (inv_nonneg.2 (Real.sqrt_nonneg _))
    _ = _ := by ring

omit [Fintype State] [DecidableEq State] in
/-- `|p − q| ≤ 1` for `p, q ∈ [0, 1]`. -/
theorem abs_sub_le_one_of_mem_unit {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : |p - q| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith

omit [DecidableEq State] in
/-- `P(Z ∈ C) ∈ [0, 1]` under the path law. -/
theorem sum_pathWeight_mul_indicator_mem_unit (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ}
    (Z : (Fin T → Tuple State Action) → State → ℝ) (C : Set (State → ℝ)) :
    0 ≤ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (Z ω) ∧
      ∑ ω : Fin T → Tuple State Action,
        pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (Z ω) ≤ 1 := by
  have hw := pathWeight_nonneg M π μ (T := T)
  have hI : ∀ ω, C.indicator (fun _ ↦ (1 : ℝ)) (Z ω) ∈ Set.Icc (0 : ℝ) 1 := fun ω ↦ by
    by_cases h : Z ω ∈ C
    · rw [Set.indicator_of_mem h]; exact ⟨zero_le_one, le_rfl⟩
    · rw [Set.indicator_of_notMem h]; exact ⟨le_rfl, zero_le_one⟩
  refine ⟨sum_nonneg fun ω _ ↦ mul_nonneg (hw ω) (hI ω).1, ?_⟩
  calc ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (Z ω)
      ≤ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω :=
        sum_le_sum fun ω _ ↦ mul_le_of_le_one_right (hw ω) (hI ω).2
    _ = 1 := sum_pathWeight M π μ T

/-- `|P(Z ∈ C) − gaussCov(C)| ≤ 1`. -/
theorem abs_sum_pathWeight_indicator_sub_gaussCov_le_one (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ}
    (Z : (Fin T → Tuple State Action) → State → ℝ) (A : Matrix State State ℝ) (Γ : State → ℝ)
    (C : Set (State → ℝ)) :
    |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (Z ω) -
        (gaussCov A Γ).real C| ≤ 1 := by
  obtain ⟨h0, h1⟩ := sum_pathWeight_mul_indicator_mem_unit M π μ Z C
  exact abs_sub_le_one_of_mem_unit h0 h1 measureReal_nonneg
    (measureReal_le_one (μ := gaussCov A Γ))

omit [Fintype State] [DecidableEq State] in
/-- For `1 ≤ T < N`: `1 ≤ N^{1/4} T^{-1/4}`, so a bound `≤ 1` is `≤ N^{1/4} T^{-1/4}`. -/
theorem one_le_rpow_quarter_mul_of_lt {T N : ℕ} (hT : 1 ≤ T) (hTN : T < N) :
    1 ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (T : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hTN' : (T : ℝ) ≤ N := by exact_mod_cast hTN.le
  rw [Real.rpow_neg hT0.le, ← div_eq_mul_inv, ← Real.div_rpow (by positivity) hT0.le]
  exact Real.one_le_rpow ((one_le_div hT0).2 hTN') (by norm_num)

omit [Fintype State] [DecidableEq State] in
/-- `T^{-1/3} ≤ T^{-1/4}` for `T ≥ 1`. -/
theorem rpow_neg_third_le_quarter {T : ℕ} (hT : 1 ≤ T) :
    (T : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (T : ℝ) ^ (-(1 / 4 : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hT) (by norm_num)

/-! ## Lower covariance bound for the target -/

/-- `uᵀ (A⁻¹ diag(Γ) A⁻ᵀ) u ≥ g ‖u‖² / (S R² + 1)` for invertible `A`, `Γ ≥ g ≥ 0`,
`R = ∑_{r,s} |A_{rs}|` (sup norm on the left). -/
theorem quadForm_target_ge (A : Matrix State State ℝ) (hA : IsUnit A.det) (Γ : State → ℝ) {g : ℝ}
    (hg0 : 0 ≤ g) (hg : ∀ r, g ≤ Γ r) (u : State → ℝ) :
    g / ((Fintype.card State : ℝ) * (∑ r, ∑ s, |A r s|) ^ 2 + 1) * ‖u‖ ^ 2 ≤
      u ⬝ᵥ ((A⁻¹ * diagonal Γ * (A⁻¹)ᵀ) *ᵥ u) := by
  set D := (Fintype.card State : ℝ) * (∑ r, ∑ s, |A r s|) ^ 2 + 1
  have hD : 0 < D := by positivity
  have h := mul_sq_sum_abs_le_quadForm A hA Γ hg0 hg u
  have hq : u ⬝ᵥ ((A⁻¹ * diagonal Γ * (A⁻¹)ᵀ) *ᵥ u) =
      ∑ r, (∑ s, u s * A⁻¹ s r) ^ 2 * Γ r := by
    rw [← quadForm_mul_diagonal_mul_transpose]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact sum_congr rfl fun s _ ↦ sum_congr rfl fun s' _ ↦ by ring
  have hn : ‖u‖ ≤ ∑ s, |u s| :=
    (pi_norm_le_iff_of_nonneg (sum_nonneg fun s _ ↦ abs_nonneg _)).2 fun s ↦ by
      rw [Real.norm_eq_abs]
      exact single_le_sum (f := fun s ↦ |u s|) (fun s _ ↦ abs_nonneg _) (mem_univ s)
  have hn2 : ‖u‖ ^ 2 ≤ (∑ s, |u s|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [hq, div_mul_eq_mul_div, div_le_iff₀ hD]
  calc g * ‖u‖ ^ 2 ≤ g * (∑ s, |u s|) ^ 2 := mul_le_mul_of_nonneg_left hn2 hg0
    _ ≤ D * ∑ r, (∑ s, u s * A⁻¹ s r) ^ 2 * Γ r := h
    _ = _ := mul_comm _ _

/-! ## `entryMax (Λ_T − Λ)` -/

/-- `entryMax (Λ_T − A⁻¹ diag(Γ_true) A⁻ᵀ) ≤ K_Λ T^{-1/3}`. -/
theorem entryMax_linCov_sub_le [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ}
    (hT : 1 ≤ T) :
    entryMax (linCov M π μ η₀ T -
        (tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * ((tdA M π μ)⁻¹)ᵀ) ≤
      linCovConst M π μ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) :=
  ciSup_le fun p ↦ by
    rw [Matrix.sub_apply]
    exact abs_linCov_sub_le M π μ h0 h1 hμmin0 hμmin hT p.1 p.2

/-! ## The comparison for large `T` -/

/-- The covariance factors `linFactor T k` assemble to `linCov`: `∑_{k : Fin T} L_k L_kᵀ = Λ_T`. -/
theorem sum_fin_linFactor_mul_transpose (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T : ℕ) :
    ∑ k : Fin T, linFactor M π μ η₀ T k * (linFactor M π μ η₀ T k)ᵀ = linCov M π μ η₀ T := by
  rw [← sum_linFactor_mul_transpose,
    Fin.sum_univ_eq_sum_range (fun k ↦ linFactor M π μ η₀ T k * (linFactor M π μ η₀ T k)ᵀ) T]

/-- The `T^{-1/4}` constant for `T ≥ linReservoirBurnIn`:
`reservoirQuarterConst S c 1 (K_β B_ξ) + gaussCmpConst S / v · K_Λ`, with
`c = min Γ_true / (32 S)` and `v = min(c, min Γ_true / (S R² + 1))`, `R = ∑ |A_{rs}|`. -/
noncomputable def linConvexQuarterConst [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (μmin η₀ : ℝ) : ℝ :=
  reservoirQuarterConst State (diagMin (trueGamma M π μ) / (32 * Fintype.card State)) 1
      (linWeightConst M μmin η₀ * tdNoiseBound M π) +
    gaussCmpConst State /
        min (diagMin (trueGamma M π μ) / (32 * Fintype.card State))
          (diagMin (trueGamma M π μ) /
            ((Fintype.card State : ℝ) * (∑ r, ∑ s, |tdA M π μ r s|) ^ 2 + 1)) *
      linCovConst M π μ μmin η₀

/-- **M6.3, large `T`.** For `T ≥ linReservoirBurnIn`, every convex `C` (measurable or not):
`|P(linPart ∈ C) − N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)(C)| ≤ linConvexQuarterConst · T^{-1/4}`. -/
theorem abs_linLaw_convex_sub_gaussCov_le_of_burnIn [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) {μmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) {T : ℕ}
    (hT : linReservoirBurnIn M μmin η₀ ≤ T) {C : Set (State → ℝ)} (hC : Convex ℝ C) :
    |∑ ω : Fin T → Tuple State Action,
        pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (linPart M π μ η₀ ω) -
        (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
      linConvexQuarterConst M π μ μmin η₀ * (T : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hT1 : 1 ≤ T := (one_le_linReservoirBurnIn M hμmin0 h0).trans hT
  have hTpos : 0 < T := hT1
  obtain ⟨hc, e, hres⟩ := exists_linFactor_reservoirCond_of_pos M π μ h0 h1 hμmin0 hμmin hΓ hT
  set c := diagMin (trueGamma M π μ) / (32 * Fintype.card State) with hc_def
  set B := linWeightConst M μmin η₀ * tdNoiseBound M π with hB_def
  set L : Fin T → Matrix State State ℝ := fun k ↦ linFactor M π μ η₀ T k with hL
  have hB : 0 ≤ B :=
    mul_nonneg (linWeightConst_nonneg M hμmin0 h0) (tdNoiseBound_pos M π).le
  -- step 1: reservoir Lindeberg for `linPart` against `twinLaw L = N(0, Λ_T)`
  have hstep1 := abs_pexp_convex_sub_twinLaw_le_quarter (X := fun _ : Fin T ↦ Tuple State Action)
    (p := fun _ ↦ tupleProb M π μ) (Y := fun k x ↦ linSummand M π μ η₀ T k x) (L := L) e hTpos
    (fun _ x ↦ tupleProb_nonneg M π μ x) (fun _ ↦ sum_tupleProb M π μ)
    (fun k a ↦ sum_tupleProb_mul_linSummand M π μ η₀ T k a)
    (fun k a b ↦ sum_tupleProb_mul_linSummand_mul M π μ η₀ T k a b) hB
    (fun k x ↦ norm_linSummand_le M π μ h0 h1 hμmin0 hμmin T k x) hc hT1 hres hC
  have hP : Stein.pexp (X := fun _ : Fin T ↦ Tuple State Action) (fun _ ↦ tupleProb M π μ)
      (fun ω ↦ C.indicator (fun _ ↦ (1 : ℝ)) (∑ i : Fin T, linSummand M π μ η₀ T i (ω i))) =
      ∑ ω : Fin T → Tuple State Action,
        pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (linPart M π μ η₀ ω) := by
    unfold Stein.pexp
    refine sum_congr rfl fun ω _ ↦ ?_
    rw [linPart_eq_sum]
    rfl
  beta_reduce at hstep1
  rw [hP] at hstep1
  -- step 2: Gaussian–Gaussian comparison `N(0, Λ_T)` vs `N(0, Λ)`
  have hA : IsUnit (tdA M π μ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)
  have hγ : 0 < diagMin (trueGamma M π μ) := (Finset.lt_inf'_iff _).2 fun s _ ↦ hΓ s
  set v₂ := diagMin (trueGamma M π μ) /
    ((Fintype.card State : ℝ) * (∑ r, ∑ s, |tdA M π μ r s|) ^ 2 + 1) with hv₂_def
  have hv₂ : 0 < v₂ := by positivity
  set v := min c v₂ with hv_def
  have hv : 0 < v := lt_min hc hv₂
  have hΓ0 : ∀ s, 0 ≤ trueGamma M π μ s := fun s ↦ (hΓ s).le
  have h₁ : ∀ u : State → ℝ, v * ‖u‖ ^ 2 ≤
      u ⬝ᵥ ((twinMat L Finset.univ * (twinMat L Finset.univ)ᵀ) *ᵥ u) := fun u ↦
    (mul_le_mul_of_nonneg_right (min_le_left c v₂) (sq_nonneg _)).trans
      (quadForm_sup_of_euclid hc.le (total_quadForm hres hT1 hTpos) u)
  have h₂ : ∀ u : State → ℝ, v * ‖u‖ ^ 2 ≤
      u ⬝ᵥ ((gaussCovFactor (tdA M π μ) (trueGamma M π μ) *
        (gaussCovFactor (tdA M π μ) (trueGamma M π μ))ᵀ) *ᵥ u) := fun u ↦ by
    rw [gaussCovFactor_mul_transpose _ hΓ0]
    exact (mul_le_mul_of_nonneg_right (min_le_right c v₂) (sq_nonneg _)).trans
      (quadForm_target_ge _ hA _ hγ.le (fun s ↦ Finset.inf'_le _ (mem_univ s)) u)
  have hstep2 := abs_real_convex_gaussian_sub_le _ _ hv h₁ h₂ hC
  rw [← gaussCov_eq_map_mulVec, twinMat_mul_transpose, gaussCovFactor_mul_transpose _ hΓ0,
    sum_fin_linFactor_mul_transpose] at hstep2
  have hE := entryMax_linCov_sub_le M π μ h0 h1 hμmin0 hμmin hT1
  have hrate := rpow_neg_third_le_quarter hT1
  have hK0 : 0 ≤ linCovConst M π μ μmin η₀ := by
    have := linWeightConst_nonneg M hμmin0 h0
    have := linRate_pos M hμmin0
    unfold linCovConst
    positivity
  have hG0 : 0 ≤ gaussCmpConst State / v := div_nonneg (gaussCmpConst_nonneg) hv.le
  have hstep2' : |(twinLaw L).real C - (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
      gaussCmpConst State / v * linCovConst M π μ μmin η₀ * (T : ℝ) ^ (-(1 / 4 : ℝ)) := by
    refine hstep2.trans ?_
    rw [mul_assoc (gaussCmpConst State / v)]
    exact mul_le_mul_of_nonneg_left (hE.trans (mul_le_mul_of_nonneg_left hrate hK0)) hG0
  calc _ ≤ |∑ ω : Fin T → Tuple State Action,
          pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (linPart M π μ η₀ ω) -
          (twinLaw L).real C| +
        |(twinLaw L).real C - (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| :=
        abs_sub_le _ _ _
    _ ≤ reservoirQuarterConst State c 1 B * (T : ℝ) ^ (-(1 / 4 : ℝ)) +
        gaussCmpConst State / v * linCovConst M π μ μmin η₀ * (T : ℝ) ^ (-(1 / 4 : ℝ)) :=
        add_le_add hstep1 hstep2'
    _ = _ := by rw [linConvexQuarterConst]; ring

/-! ## Main export -/

/-- **M6.3: the linearised TD statistic over all convex sets at `T^{-1/4}`** (infrastructure;
**partial, not a source result**). For full-support `μ`, `0 < η₀ ≤ 1` and `Γ_true ≻ 0` there is an
instance constant `K > 0` such that for every `T ≥ 1` and every convex `C ⊆ ℝ^S` (measurable or
not; `gaussCov.real` is the outer measure)
`|P(linPart_T ∈ C) − N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)(C)| ≤ K T^{-1/4}`.

This concerns only the linearised statistic `X^lin_T` (not `√T Δ̄_T`), at the rate `T^{-1/4}`
(not the printed `T^{-1/3}` of `thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`), with
the corrected covariance `Γ_true` (SOURCE-ISSUES C43) and an instance-dependent constant. It is not
Theorem 7.11 and has no statement-index entry. -/
theorem abs_linLaw_convex_sub_gaussCov_le_quarter [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C →
      |∑ ω : Fin T → Tuple State Action,
          pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (linPart M π μ η₀ ω) -
          (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
        K * (T : ℝ) ^ (-(1 / 4 : ℝ)) := by
  set μmin := diagMin μ.prob with hμmin_def
  have hμmin0 : 0 < μmin := (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s
  have hμmin : ∀ s, μmin ≤ μ.prob s := fun s ↦ Finset.inf'_le _ (mem_univ s)
  set N := linReservoirBurnIn M μmin η₀
  set K₁ := linConvexQuarterConst M π μ μmin η₀
  set K := |K₁| + (N : ℝ) ^ (1 / 4 : ℝ) + 1 with hK_def
  have hN0 : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨K, by positivity, fun T hT C hC ↦ ?_⟩
  have hTr : 0 ≤ (T : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hTN : N ≤ T
  · refine (abs_linLaw_convex_sub_gaussCov_le_of_burnIn M π μ h0 h1 hμmin0 hμmin hΓ hTN
      hC).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hTr
    have := le_abs_self K₁
    linarith
  · have h1' := abs_sum_pathWeight_indicator_sub_gaussCov_le_one M π μ (T := T)
      (fun ω ↦ linPart M π μ η₀ ω) (tdA M π μ) (trueGamma M π μ) C
    have h2 := one_le_rpow_quarter_mul_of_lt hT (not_le.1 hTN)
    refine h1'.trans (h2.trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ hTr
    have := abs_nonneg K₁
    linarith

end StatisticalRL.Ch7Rest.TDInference

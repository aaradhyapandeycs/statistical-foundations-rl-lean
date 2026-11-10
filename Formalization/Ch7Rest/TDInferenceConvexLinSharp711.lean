import Formalization.Ch7Rest.TDInferenceConvexLin711
import Formalization.Probability.ConvexLindebergReservoirSharp

/-!
# Partial result toward Theorem 7.11 (not the printed result): the linearised statistic over all convex sets at `T^{-1/3}`

Infrastructure for the all-convex-sets route to `thm:Berry-Esseen-linear`
(`chapters/inference.tex:132–141`; `d_cvx` at :124–127; `Λ⋆ = A⁻¹ΓA⁻ᵀ` at :104–117, with
`Γ := Γ_true`, SOURCE-ISSUES C43). **No source result is claimed here and there is no
statement-index entry.** The printed theorem is about the full statistic `√T Δ̄_T`; this module
concerns only the linearised statistic `linPart` (`X^lin_T = T^{-1/2} ∑_k linSummand_k`), now at
the printed rate `T^{-1/3}`, with an instance constant (not the printed coefficient). It is not
Theorem 7.11: the nonlinear remainder `√T Δ̄_T − X^lin_T` is not treated here.

Route: as `TDInferenceConvexLin711.lean`, with the pass-2 reservoir Lindeberg bound
`ReservoirSharp.abs_pexp_convex_sub_twinLaw_le_third` (rate `n^{-1/3}`, no `r₀ ≤ n` hypothesis) in
place of pass 1, followed by the Gaussian–Gaussian comparison `abs_real_convex_gaussian_sub_le`,
whose error `entryMax (Λ_T − Λ) = O(T^{-1/3})` already has the right rate.

Main export: `abs_linLaw_convex_sub_gaussCov_le_third`.
-/

open Finset Matrix MeasureTheory Metric
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-- The `T^{-1/3}` constant for `T ≥ linReservoirBurnIn`:
`reservoirThirdConst S c 1 (K_β B_ξ) + gaussCmpConst S / v · K_Λ`, with
`c = min Γ_true / (32 S)` and `v = min(c, min Γ_true / (S R² + 1))`, `R = ∑ |A_{rs}|`. -/
noncomputable def linConvexThirdConst [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (μmin η₀ : ℝ) : ℝ :=
  ReservoirSharp.reservoirThirdConst State (diagMin (trueGamma M π μ) / (32 * Fintype.card State))
      1 (linWeightConst M μmin η₀ * tdNoiseBound M π) +
    gaussCmpConst State /
        min (diagMin (trueGamma M π μ) / (32 * Fintype.card State))
          (diagMin (trueGamma M π μ) /
            ((Fintype.card State : ℝ) * (∑ r, ∑ s, |tdA M π μ r s|) ^ 2 + 1)) *
      linCovConst M π μ μmin η₀

/-- **Large `T`.** For `T ≥ linReservoirBurnIn`, every convex `C` (measurable or not):
`|P(linPart ∈ C) − N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)(C)| ≤ linConvexThirdConst · T^{-1/3}`. -/
theorem abs_linLaw_convex_sub_gaussCov_le_third_of_burnIn [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) {μmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) {T : ℕ}
    (hT : linReservoirBurnIn M μmin η₀ ≤ T) {C : Set (State → ℝ)} (hC : Convex ℝ C) :
    |∑ ω : Fin T → Tuple State Action,
        pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (linPart M π μ η₀ ω) -
        (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
      linConvexThirdConst M π μ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hT1 : 1 ≤ T := (one_le_linReservoirBurnIn M hμmin0 h0).trans hT
  have hTpos : 0 < T := hT1
  obtain ⟨hc, e, hres⟩ := exists_linFactor_reservoirCond_of_pos M π μ h0 h1 hμmin0 hμmin hΓ hT
  set c := diagMin (trueGamma M π μ) / (32 * Fintype.card State) with hc_def
  set B := linWeightConst M μmin η₀ * tdNoiseBound M π with hB_def
  set L : Fin T → Matrix State State ℝ := fun k ↦ linFactor M π μ η₀ T k with hL
  have hB : 0 ≤ B :=
    mul_nonneg (linWeightConst_nonneg M hμmin0 h0) (tdNoiseBound_pos M π).le
  -- step 1: pass-2 reservoir Lindeberg for `linPart` against `twinLaw L = N(0, Λ_T)`
  have hstep1 := ReservoirSharp.abs_pexp_convex_sub_twinLaw_le_third
    (X := fun _ : Fin T ↦ Tuple State Action)
    (p := fun _ ↦ tupleProb M π μ) (Y := fun k x ↦ linSummand M π μ η₀ T k x) (L := L) e hTpos
    (fun _ x ↦ tupleProb_nonneg M π μ x) (fun _ ↦ sum_tupleProb M π μ)
    (fun k a ↦ sum_tupleProb_mul_linSummand M π μ η₀ T k a)
    (fun k a b ↦ sum_tupleProb_mul_linSummand_mul M π μ η₀ T k a b) hB
    (fun k x ↦ norm_linSummand_le M π μ h0 h1 hμmin0 hμmin T k x) hc hres hC
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
  have hG0 : 0 ≤ gaussCmpConst State / v := div_nonneg (gaussCmpConst_nonneg) hv.le
  have hstep2' : |(twinLaw L).real C - (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
      gaussCmpConst State / v * linCovConst M π μ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
    refine hstep2.trans ?_
    rw [mul_assoc (gaussCmpConst State / v)]
    exact mul_le_mul_of_nonneg_left hE hG0
  calc _ ≤ |∑ ω : Fin T → Tuple State Action,
          pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (linPart M π μ η₀ ω) -
          (twinLaw L).real C| +
        |(twinLaw L).real C - (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| :=
        abs_sub_le _ _ _
    _ ≤ ReservoirSharp.reservoirThirdConst State c 1 B * (T : ℝ) ^ (-(1 / 3 : ℝ)) +
        gaussCmpConst State / v * linCovConst M π μ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) :=
        add_le_add hstep1 hstep2'
    _ = _ := by rw [linConvexThirdConst]; ring

/-- **The linearised TD statistic over all convex sets at `T^{-1/3}`** (infrastructure toward
Theorem 7.11; **partial, not a source result, no statement-index entry**). For full-support `μ`,
`0 < η₀ ≤ 1` and `Γ_true ≻ 0` there is an instance constant `K > 0` such that for every `T ≥ 1`
and every convex `C ⊆ ℝ^S` (measurable or not; `gaussCov.real` is the outer measure)
`|P(linPart_T ∈ C) − N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)(C)| ≤ K T^{-1/3}`.

This concerns only the linearised statistic `X^lin_T` (not `√T Δ̄_T`), with the corrected
covariance `Γ_true` (SOURCE-ISSUES C43) and an instance-dependent constant (not the printed
coefficient of `thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`). It is not Theorem 7.11.
Same hypotheses as `abs_linLaw_convex_sub_gaussCov_le_quarter`, rate improved from `T^{-1/4}`. -/
theorem abs_linLaw_convex_sub_gaussCov_le_third [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C →
      |∑ ω : Fin T → Tuple State Action,
          pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (linPart M π μ η₀ ω) -
          (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
        K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  set μmin := diagMin μ.prob with hμmin_def
  have hμmin0 : 0 < μmin := (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s
  have hμmin : ∀ s, μmin ≤ μ.prob s := fun s ↦ Finset.inf'_le _ (mem_univ s)
  set N := linReservoirBurnIn M μmin η₀
  set K₁ := linConvexThirdConst M π μ μmin η₀
  set K := |K₁| + (N : ℝ) ^ (1 / 3 : ℝ) + 1 with hK_def
  have hN0 : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨K, by positivity, fun T hT C hC ↦ ?_⟩
  have hTr : 0 ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hTN : N ≤ T
  · refine (abs_linLaw_convex_sub_gaussCov_le_third_of_burnIn M π μ h0 h1 hμmin0 hμmin hΓ hTN
      hC).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hTr
    have := le_abs_self K₁
    linarith
  · have h1' := abs_sum_pathWeight_indicator_sub_gaussCov_le_one M π μ (T := T)
      (fun ω ↦ linPart M π μ η₀ ω) (tdA M π μ) (trueGamma M π μ) C
    have h2 := ReservoirSharp.one_le_rpow_third_mul_of_lt hT (not_le.1 hTN)
    refine h1'.trans (h2.trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ hTr
    have := abs_nonneg K₁
    linarith

end StatisticalRL.Ch7Rest.TDInference

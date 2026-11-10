import Formalization.Ch7Rest.TDInferenceConvexLog711
import Formalization.Ch7Rest.TDInferenceConvexLinSharp711

/-!
# Partial result toward Theorem 7.11 (not the printed result): the TD estimate over all convex sets at `T^{-1/3} log(2T)`

Source: Theorem 7.11 (`thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`; convex distance
`d_cvx` at :124–127; `Λ⋆ = A⁻¹ΓA⁻ᵀ` at :104–117).

**This is a partial result, not Theorem 7.11 and not a statement-index entry.** It bounds the
convex distance between the law of the full statistic `√T Δ̄_T` and `N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)`
by `K · T^{-1/3} · log(2T)`, uniformly over all convex sets. Compared with the printed theorem:
* the rate carries an extra factor `log(2T)` (the printed rate is `T^{-1/3}`);
* the constant `K` is an instance constant (it may depend on `M, π, μ, η₀, V₀`), not the printed
  coefficient times a universal constant;
* the covariance is the corrected `Γ_true` (SOURCE-ISSUES C43), assumed positive definite;
* the hypothesis `0 < η₀ ≤ 1` is more general than the printed `0 < η₀ < 1/4`.

Proof: the transfer theorem `abs_lawProb_convex_sub_gaussCov_le_of_linRate` (a convex-set rate
`T^{-a}` for the linear part gives `K (T^{-a} + T^{-1/3} log(2T))` for the full statistic) applied
with `a = 1/3`, using the linear-part bound `abs_linLaw_convex_sub_gaussCov_le_third`.
-/

open Finset Matrix MeasureTheory

namespace StatisticalRL.Ch7Rest.TDInference

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-- **Partial result toward Theorem 7.11 (not the printed result): all convex sets at
`T^{-1/3} log(2T)`** (infrastructure, no statement-index entry). For full-support `μ`,
`0 < η₀ ≤ 1`, every initial value `V₀` and `Γ_true ≻ 0`, there is an instance constant `K > 0`
such that for every `T ≥ 1` and every convex `C` (measurable or not; the Gaussian side is the
outer measure),
`|P(√T Δ̄_T ∈ C) − N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)(C)| ≤ K · T^{-1/3} · log(2T)`.
The printed rate `T^{-1/3}` without the logarithm is proved separately, by a different remainder argument, in
`TDInferenceConvexSharp711.lean` (`abs_lawProb_convex_sub_gaussCov_le_third_sharp`, statement entry
`Thm7_11_corrected`); this weaker bound is kept because the oracle confidence-region corollaries use it. -/
theorem abs_lawProb_convex_sub_gaussCov_le_third_log [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
        K * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)) := by
  obtain ⟨K₁, -, hK₁⟩ := abs_linLaw_convex_sub_gaussCov_le_third M π μ h0 h1 hμ hΓ
  obtain ⟨K, hK, hb⟩ := abs_lawProb_convex_sub_gaussCov_le_of_linRate M π μ h0 h1 V₀ hμ hΓ
    (1 / 3 : ℝ) ⟨K₁, hK₁⟩
  refine ⟨K * (1 / Real.log 2 + 1), by positivity, fun T hT C hC ↦ ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (2 * T) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hr : 0 ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (by positivity) _
  -- `T^{-1/3} ≤ T^{-1/3} log(2T) / log 2`
  have h1' : (T : ℝ) ^ (-(1 / 3 : ℝ)) ≤
      (1 / Real.log 2) * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)) := by
    rw [← mul_assoc, mul_comm (1 / Real.log 2), mul_assoc]
    have : 1 ≤ (1 / Real.log 2) * Real.log (2 * T) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hl2, one_mul]; exact hlog
    nlinarith
  calc |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (trueGamma M π μ)).real C|
      ≤ K * ((T : ℝ) ^ (-(1 / 3 : ℝ)) + (T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)) :=
        hb T hT C hC
    _ ≤ K * ((1 / Real.log 2) * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)) +
          (T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)) := by gcongr
    _ = K * (1 / Real.log 2 + 1) * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)) := by ring

end StatisticalRL.Ch7Rest.TDInference

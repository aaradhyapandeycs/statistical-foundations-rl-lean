import Formalization.TDInference.ConvexSets.Sharp
import Formalization.TDInference.Confidence.ChiSquareQuantile

/-!
# Oracle-covariance confidence regions at the printed rate `T^{-1/3}`

Source: `chapters/inference.tex:187–213` (rule `eq:convex.Cdelta` :189–196, rectangles :198–205,
ellipsoids :207–213) and `docs/SOURCE-ISSUES.md` C47, C43. These are **corrected and
oracle-restricted forms, not the printed formulas**, and a **partial** result for
`eq:convex.Cdelta`.

This file repeats the three oracle-covariance corollaries

* `exists_confRegion_oracle_bounds` (fixed convex shape, corrected ellipsoid, corrected rectangle),
* `exists_confRegion_oracle_calibrated` (exact Gaussian `1 − α` levels),
* `exists_confRegion_oracle_chiSquared` (ellipsoid threshold at the `χ²(S)` quantile),

at the rate `K₀ T^{-1/3}` instead of `K₀ T^{-1/3} log(2T)`. The only change is the convex-set
input: `abs_lawProb_convex_sub_gaussCov_le_third_sharp` (`TDInference/ConvexSets/Sharp.lean`) in place
of `abs_lawProb_convex_sub_gaussCov_le_third_log`. The event identities, Gaussian symmetry,
convexity of the corrected sets and exact levels are reused from `TDInferenceConfRegion711`,
`TDInferenceConfCalib711` and `TDInferenceConfChiSq711`.

Still not the printed rule: the covariance is the **oracle** `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`
(`trueLambda`, unknown in practice; the printed plug-in `Λ̂_T` with a rate remains open), the
shapes are the C47 corrections (fixed shape; ellipsoid threshold `q`, not `q²`; rectangle
half-width `r/√T`), and `K₀` is an instance constant (it may depend on `M, π, μ, η₀, V₀`).
-/

open MeasureTheory ProbabilityTheory Finset Matrix
open scoped BigOperators Pointwise
open StatisticalRL.Probability

namespace StatisticalRL.Ch7Rest.TDInference

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-- **Oracle-covariance confidence regions at `T^{-1/3}` (corrected forms, partial for
`eq:convex.Cdelta`).** For full-support `μ`, `0 < η₀ ≤ 1`, every `V₀` and `Γ_true ≻ 0`, with
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (`trueLambda`, the oracle covariance, unknown in practice), there is one
instance constant `K₀ > 0` such that for all `T ≥ 1`:
1. every convex `K` (fixed before the data):
   `|P(V^π ∈ V̄_T + T^{-1/2} K) − N(0,Λ)(K)| ≤ K₀ T^{-1/3}`;
2. every `q` (ellipsoid corrected per C47(3), threshold `q`):
   `|P(T (V^π − V̄_T)ᵀ Λ⁻¹ (V^π − V̄_T) ≤ q) − N(0,Λ){xᵀΛ⁻¹x ≤ q}| ≤ K₀ T^{-1/3}`;
3. every `r` (rectangle corrected per C47(2), half-width `r/√T`):
   `|P(∀ s, V̄_T(s) − r/√T ≤ V^π(s) ≤ V̄_T(s) + r/√T) − N(0,Λ){‖x‖∞ ≤ r}| ≤ K₀ T^{-1/3}`.
Same statement as `exists_confRegion_oracle_bounds` without the factor `log(2T)`. -/
theorem exists_confRegion_oracle_bounds_sharp [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) (hμ : ∀ s, 0 < μ.prob s)
    (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ T : ℕ, 1 ≤ T →
      (∀ K : Set (State → ℝ), Convex ℝ K →
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action |
              M.valueFixedPoint π ∈ prAverage M η₀ V₀ ω' +ᵥ (Real.sqrt T)⁻¹ • K}.indicator 1 ω -
          (gaussCov (tdA M π μ) (trueGamma M π μ)).real K| ≤
          K₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (∀ q : ℝ,
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
              (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
                (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                  (trueLambda M π μ)⁻¹ s s' ≤ q}.indicator 1 ω -
          (gaussCov (tdA M π μ) (trueGamma M π μ)).real
            {x | ∑ s, ∑ s', x s * x s' * (trueLambda M π μ)⁻¹ s s' ≤ q}| ≤
          K₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (∀ r : ℝ,
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∀ s,
              prAverage M η₀ V₀ ω' s - r / Real.sqrt T ≤ M.valueFixedPoint π s ∧
                M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + r / Real.sqrt T}.indicator 1 ω -
          (gaussCov (tdA M π μ) (trueGamma M π μ)).real {x | ∀ s, |x s| ≤ r}| ≤
          K₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨K₀, hK₀, hb⟩ := abs_lawProb_convex_sub_gaussCov_le_third_sharp M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K₀, hK₀, fun T hT ↦ ⟨fun K hK ↦ ?_, fun q ↦ ?_, fun r ↦ ?_⟩⟩
  · rw [sum_pathWeight_fixedShape_eq_lawProb M π μ η₀ V₀ hT K, ← gaussCov_real_neg _ _ K]
    exact hb T hT (-K) hK.neg
  · rw [sum_pathWeight_ellipsoid_eq_lawProb M π μ η₀ V₀ T]
    exact hb T hT _ (convex_trueLambda_ellipsoid M π μ hμ hΓ q)
  · rw [sum_pathWeight_supRect_eq_lawProb M π μ η₀ V₀ hT r]
    exact hb T hT _ (convex_supBox r)

section TD

variable [Nonempty State] (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
  (μ : FiniteDistribution State)

/-- **Calibrated oracle-covariance confidence regions at `T^{-1/3}` (corrected C47(2)/(3)).**
For full-support `μ`, `0 < η₀ ≤ 1`, every `V₀`, `Γ_true ≻ 0` and `S ≥ 1`, with
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (oracle covariance, unknown in practice), there is one instance
constant `K₀ > 0` such that for every `α ∈ (0,1)` there are levels `q_α ≥ 0`, `r_α ≥ 0`
(independent of `T`) with `N(0,Λ){xᵀΛ⁻¹x ≤ q_α} = 1 − α`, `N(0,Λ){‖x‖∞ ≤ r_α} = 1 − α`, and for
all `T ≥ 1`:
`|P(T (V^π − V̄_T)ᵀ Λ⁻¹ (V^π − V̄_T) ≤ q_α) − (1 − α)| ≤ K₀ T^{-1/3}` and
`|P(∀ s, V̄_T(s) − r_α/√T ≤ V^π(s) ≤ V̄_T(s) + r_α/√T) − (1 − α)| ≤ K₀ T^{-1/3}`.
Same statement as `exists_confRegion_oracle_calibrated` without the factor `log(2T)`. -/
theorem exists_confRegion_oracle_calibrated_sharp (hμ : ∀ s, 0 < μ.prob s) {η₀ : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ α : ℝ, 0 < α → α < 1 →
      ∃ q : ℝ, 0 ≤ q ∧ ∃ r : ℝ, 0 ≤ r ∧
        (gaussCov (tdA M π μ) (trueGamma M π μ)).real
          {x | ∑ s, ∑ s', x s * x s' * (trueLambda M π μ)⁻¹ s s' ≤ q} = 1 - α ∧
        (gaussCov (tdA M π μ) (trueGamma M π μ)).real {x | ∀ s, |x s| ≤ r} = 1 - α ∧
        ∀ T : ℕ, 1 ≤ T →
          |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
              {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
                (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
                  (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                    (trueLambda M π μ)⁻¹ s s' ≤ q}.indicator 1 ω - (1 - α)| ≤
            K₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) ∧
          |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
              {ω' : Fin T → Tuple State Action | ∀ s,
                prAverage M η₀ V₀ ω' s - r / Real.sqrt T ≤ M.valueFixedPoint π s ∧
                  M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + r / Real.sqrt T}.indicator 1 ω -
              (1 - α)| ≤
            K₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K₀, hK₀, hb⟩ := exists_confRegion_oracle_bounds_sharp M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K₀, hK₀, fun α hα0 hα1 ↦ ?_⟩
  obtain ⟨q, hq0, hq⟩ := exists_ellipsoid_level_eq M π μ hμ hΓ hα0 hα1
  obtain ⟨r, hr0, hr⟩ := exists_supBox_level_eq M π μ hμ hΓ hα0 hα1
  refine ⟨q, hq0, r, hr0, hq, hr, fun T hT ↦ ⟨?_, ?_⟩⟩
  · rw [← hq]; exact (hb T hT).2.1 q
  · rw [← hr]; exact (hb T hT).2.2 r

/-- **Calibrated oracle ellipsoid at the printed `χ²(S)` quantile, rate `T^{-1/3}` (corrected
C47(3)).** For full-support `μ`, `0 < η₀ ≤ 1`, every `V₀`, `Γ_true ≻ 0` and `S ≥ 1`, with
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (oracle covariance), there is one instance constant `K₀ > 0` such
that for every `α ∈ (0,1)` and every `1 − α` quantile `q` of `χ²(S)`:
`N(0,Λ){xᵀΛ⁻¹x ≤ q} = 1 − α`, and for all `T ≥ 1`,
`|P(T (V^π − V̄_T)ᵀ Λ⁻¹ (V^π − V̄_T) ≤ q) − (1 − α)| ≤ K₀ T^{-1/3}`.
Same statement as `exists_confRegion_oracle_chiSquared` without the factor `log(2T)`. -/
theorem exists_confRegion_oracle_chiSquared_sharp (hμ : ∀ s, 0 < μ.prob s) {η₀ : ℝ}
    (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ α : ℝ, 0 < α → α < 1 → ∀ q : ℝ,
      cdf (chiSquared (Fintype.card State)) q = 1 - α →
        (gaussCov (tdA M π μ) (trueGamma M π μ)).real
          {x | ∑ s, ∑ s', x s * x s' * (trueLambda M π μ)⁻¹ s s' ≤ q} = 1 - α ∧
        ∀ T : ℕ, 1 ≤ T →
          |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
              {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
                (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
                  (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                    (trueLambda M π μ)⁻¹ s s' ≤ q}.indicator 1 ω - (1 - α)| ≤
            K₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K₀, hK₀, hb⟩ := exists_confRegion_oracle_bounds_sharp M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K₀, hK₀, fun α _ _ q hq ↦ ?_⟩
  have hN := (gaussCov_ellipsoid_eq_chiSquared M π μ hμ hΓ q).trans hq
  refine ⟨hN, fun T hT ↦ ?_⟩
  rw [← hN]
  exact (hb T hT).2.1 q

end TD

end StatisticalRL.Ch7Rest.TDInference

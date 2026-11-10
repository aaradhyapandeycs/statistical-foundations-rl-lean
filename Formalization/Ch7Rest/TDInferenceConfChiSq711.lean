import Formalization.Probability.ChiSquaredQuadForm
import Formalization.Probability.GaussianCovCompare
import Formalization.Ch7Rest.TDInferenceConfCalib711

/-!
# The corrected TD confidence ellipsoid at the printed `χ²(S)` quantile

Source: `chapters/inference.tex:207–213` (ellipsoids: "`R` is the `1 − α` quantile of the
`χ²(d)` distribution") and `docs/SOURCE-ISSUES.md` C47(3). These are **corrected and
oracle-restricted forms, not the printed formula**: the dimension is `d = S = |State|`, the
threshold of the quadratic form is the quantile `R` itself (not `R²`), the covariance is the
**oracle** `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (`trueLambda`, unknown in practice; the plug-in `Λ̂_T` is not
treated), and the rate carries the extra factor `log(2T)` of `exists_confRegion_oracle_bounds`.

* `gaussCov_ellipsoid_eq_chiSquared`: under full-support `μ` and `Γ_true ≻ 0`,
  `N(0,Λ){x | xᵀΛ⁻¹x ≤ q} = F_{χ²(S)}(q)` for every real `q`
  (`N(0,Λ) = gaussCov (tdA M π μ) (trueGamma M π μ)`, `χ²(S) = chiSquared S`);
* `exists_chiSquared_quantile`: for `k ≥ 1` and `α ∈ (0,1)` some `q ≥ 0` has
  `F_{χ²(k)}(q) = 1 − α` (`χ²(k)` has a density, so its cdf is continuous);
* `exists_confRegion_oracle_chiSquared`: one instance constant `K₀ > 0` such that for every
  `α ∈ (0,1)` and **every** `q` with `F_{χ²(S)}(q) = 1 − α` (a `1 − α` quantile of `χ²(S)`),
  `N(0,Λ){xᵀΛ⁻¹x ≤ q} = 1 − α` and for all `T ≥ 1`
  `|P(T (V^π − V̄_T)ᵀ Λ⁻¹ (V^π − V̄_T) ≤ q) − (1 − α)| ≤ K₀ T^{-1/3} log(2T)`.
  So the exact level `q_α` of `exists_confRegion_oracle_calibrated` can be taken to be the
  printed `χ²(S)` quantile.
-/

open MeasureTheory ProbabilityTheory Finset Matrix Set
open StatisticalRL.Probability

namespace StatisticalRL.Ch7Rest.TDInference

/-- **`χ²(k)` quantiles exist.** For `k ≥ 1` and `α ∈ (0,1)` there is `q ≥ 0` with
`F_{χ²(k)}(q) = 1 − α`. -/
theorem exists_chiSquared_quantile {k : ℕ} (hk : 0 < k) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ cdf (chiSquared k) q = 1 - α := by
  haveI := isProbabilityMeasure_chiSquared hk
  have hac : chiSquared k ≪ volume := withDensity_absolutelyContinuous _ _
  have hatom : ∀ q : ℝ, chiSquared k {x | x = q} = 0 := fun q ↦ by
    rw [setOf_eq_eq_singleton]
    exact hac (Real.volume_singleton)
  have hneg : chiSquared k (Iio 0) = 0 := by
    rw [chiSquared, gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  have h0 : chiSquared k {x : ℝ | x ≤ 0} = 0 := by
    refine measure_mono_null (fun x hx ↦ ?_) (measure_union_null hneg (hatom 0))
    rcases (show x ≤ 0 from hx).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨q, hq0, hq⟩ := confCalib_exists_level_eq (chiSquared k) (g := fun x : ℝ ↦ x)
    measurable_id hatom h0 (p := 1 - α) (by linarith) (by linarith)
  exact ⟨q, hq0, by rw [cdf_eq_real]; exact hq⟩

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]
  [Nonempty State] (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
  (μ : FiniteDistribution State)

/-- **The oracle Gaussian mass of the corrected ellipsoid is the `χ²(S)` cdf (C47(3)).** For
full-support `μ` and `Γ_true ≻ 0`, with `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` and `S = |State| ≥ 1`,
`N(0,Λ){x | xᵀΛ⁻¹x ≤ q} = F_{χ²(S)}(q)` for every real `q`. -/
theorem gaussCov_ellipsoid_eq_chiSquared (hμ : ∀ s, 0 < μ.prob s)
    (hΓ : ∀ s, 0 < trueGamma M π μ s) (q : ℝ) :
    (gaussCov (tdA M π μ) (trueGamma M π μ)).real
        {x | ∑ s, ∑ s', x s * x s' * (trueLambda M π μ)⁻¹ s s' ≤ q} =
      cdf (chiSquared (Fintype.card State)) q := by
  have hA : IsUnit (tdA M π μ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ
      (μmin := Finset.univ.inf' Finset.univ_nonempty μ.prob)
      ((Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s) (fun s ↦ Finset.inf'_le _ (mem_univ s)))
  have hL : IsUnit (gaussCovFactor (tdA M π μ) (trueGamma M π μ)).det := by
    rw [gaussCovFactor, det_mul, det_diagonal]
    exact (isUnit_nonsing_inv_det _ hA).mul (isUnit_iff_ne_zero.2
      (Finset.prod_ne_zero_iff.2 fun s _ ↦ (Real.sqrt_pos.2 (hΓ s)).ne'))
  have hΛ : trueLambda M π μ = gaussCovFactor (tdA M π μ) (trueGamma M π μ) *
      (gaussCovFactor (tdA M π μ) (trueGamma M π μ))ᵀ :=
    (gaussCovFactor_mul_transpose (tdA M π μ) fun s ↦ (hΓ s).le).symm
  rw [hΛ, gaussCov_eq_map_mulVec]
  exact map_mulVec_stdGaussianPi_quadForm_le_real _ hL q

/-- **Calibrated oracle ellipsoid at the printed `χ²(S)` quantile (corrected C47(3), extra
`log(2T)`).** For full-support `μ`, `0 < η₀ ≤ 1`, every `V₀`, `Γ_true ≻ 0` and `S ≥ 1`, with
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (oracle covariance), there is one instance constant `K₀ > 0` such
that for every `α ∈ (0,1)` and every `1 − α` quantile `q` of `χ²(S)` (`F_{χ²(S)}(q) = 1 − α`;
one exists by `exists_chiSquared_quantile`): `N(0,Λ){xᵀΛ⁻¹x ≤ q} = 1 − α`, and for all `T ≥ 1`,
`|P(T (V^π − V̄_T)ᵀ Λ⁻¹ (V^π − V̄_T) ≤ q) − (1 − α)| ≤ K₀ T^{-1/3} log(2T)`.
Not the printed formula: threshold `q` (the quantile itself) instead of `R²`, oracle `Λ`, and the
rate has the extra factor `log(2T)`. -/
theorem exists_confRegion_oracle_chiSquared (hμ : ∀ s, 0 < μ.prob s) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
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
            K₀ * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)) := by
  obtain ⟨K₀, hK₀, hb⟩ := exists_confRegion_oracle_bounds M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K₀, hK₀, fun α _ _ q hq ↦ ?_⟩
  have hN := (gaussCov_ellipsoid_eq_chiSquared M π μ hμ hΓ q).trans hq
  refine ⟨hN, fun T hT ↦ ?_⟩
  rw [← hN]
  exact (hb T hT).2.1 q

end StatisticalRL.Ch7Rest.TDInference

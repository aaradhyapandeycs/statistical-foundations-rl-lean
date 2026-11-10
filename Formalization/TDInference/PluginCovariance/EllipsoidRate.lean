import Formalization.TDInference.PluginCovariance.Rate
import Formalization.TDInference.PluginCovariance.Ellipsoid
import Formalization.TDInference.Confidence.RegionsSharp
import Formalization.Probability.GaussianConvexCompare

/-!
# Plug-in-covariance confidence ellipsoid at the finite-`T` rate `T^{-1/3}` (corrected C47(3))

Source: `chapters/inference.tex:207–213` (ellipsoids from `eq:convex.Cdelta` :187–196, "`R` is the
`1 − α` quantile of the `χ²(d)` distribution"), the plug-in covariance `eq:defn-hat-Lambda`
(`inference.tex:180–182`), and `docs/SOURCE-ISSUES.md` C47(3), C47(4), C43.

With the **printed plug-in covariance** `Λ̂_T = Ā_T⁻¹ Γ̂_T Ā_T⁻ᵀ` (`lambdaHat`), the
Polyak–Ruppert average `V̄_T` (`prAverage`) and `S = |State|`:

* `exists_coverage_ellipsoid_plugin_rate`: one instance constant `K > 0` such that for every
  `T ≥ 1` and **every** real `q`,
  `|P(T (V^π − V̄_T)ᵀ Λ̂_T⁻¹ (V^π − V̄_T) ≤ q) − F_{χ²(S)}(q)| ≤ K T^{-1/3}`;
* `exists_coverage_ellipsoid_plugin_chiSquared_rate`: with the same kind of constant, for every
  `α ∈ (0,1)`, every `1 − α` quantile `R` of `χ²(S)` and every `T ≥ 1`,
  `|P(T (V^π − V̄_T)ᵀ Λ̂_T⁻¹ (V^π − V̄_T) ≤ R) − (1 − α)| ≤ K T^{-1/3}`.

Hypotheses: full-support `μ`, `0 < η₀ ≤ 1` (containing the printed `(0, 1/4)`), every `V₀`,
`Γ_true ≻ 0` (added non-degeneracy hypothesis). By C43 the limit covariance of `Λ̂_T` is the
corrected `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (`trueLambda`).

**Corrected shape (C47(3)).** The threshold of the quadratic form is the quantile `R` itself
(not `R²`), and the `√T` scaling is applied once, to the deviation.

**Constant.** `K` is an instance constant: it depends on `M, π, μ, η₀, V₀` only, and is
independent of `T`, of the threshold `q`, and (in the corollary) of `α` and `R`. Explicitly
`K = K₀ + C + K_g C_e + 2 C_e`, where `K₀` is the sharp oracle convex-set constant
(`abs_lawProb_convex_sub_gaussCov_le_third_sharp`), `C` the plug-in constant of
`exists_pathProb_lambdaHat_inv_sub_gt_le`, `C_e` the norm-equivalence constant
`(∑|x_s|)² ≤ C_e xᵀΛ⁻¹x`, and `K_g = 2 gaussCmpConst(S) / v₀ · max_{s,s'} |Λ(s,s')|`
with `v₀ = min_s Γ_true(s) / (S (∑|A|)² + 1)` the ellipticity of `Λ`. It is not the printed
coefficient (none is printed for the plug-in rule).

**Route.** Put `ε = T^{-1/3}`, `κ = C_e ε`. Off the bad event
`{∃ s s', ε < |Λ̂_T⁻¹(s,s') − Λ⁻¹(s,s')|}` (probability `≤ C/(ε²T) = C T^{-1/3}`) the plug-in form
is within relative error `κ` of the oracle form, so for `κ ≤ 1/2` the plug-in event is
sandwiched between the oracle ellipsoids at `q/(1 + κ)` and `q/(1 − κ)`, whose probabilities are
within `K₀ T^{-1/3}` of `N(0,Λ)`-masses (sharp convex Berry–Esseen). The Gaussian side is uniform
in `q` by **scaling**: `N(0,Λ){Q ≤ q/c} = N(0,cΛ){Q ≤ q}`
(`map_smul_mulVec_real_quadForm_le`), and the Gaussian–Gaussian convex comparison
`abs_real_convex_gaussian_sub_le` bounds `|N(0,cΛ)(K) − N(0,Λ)(K)| ≤ K_g |c − 1|` for `c ≥ 1/2`.
For `κ > 1/2` the bound is trivial (`1 ≤ 2κ`). No `χ²` density bound is used.

**Junk value (C47(4)).** On outcomes where `Ā_T` or `Λ̂_T` is singular, Lean's `Matrix.inv`
returns `0`; such outcomes lie inside the bad event (charged quantitatively by
`exists_pathProb_lambdaHat_inv_sub_gt_le`), so the bound does not depend on the junk convention.
-/

open MeasureTheory ProbabilityTheory Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability

/-! ## Gaussian side: scaling of the ellipsoid threshold -/

section Scaling

variable {ι : Type} [Fintype ι]

/-- **Scaling the threshold of a quadratic-form sublevel set.** For `c > 0`, the law of
`(√c F) Z` (`Z` standard Gaussian) gives `{xᵀPx ≤ q}` the same mass as the law of `F Z` gives
`{xᵀPx ≤ q/c}`. -/
theorem map_smul_mulVec_real_quadForm_le (F P : Matrix ι ι ℝ) {c : ℝ} (hc : 0 < c) (q : ℝ) :
    ((stdGaussianPi ι).map ((Real.sqrt c • F) *ᵥ ·)).real
        {x | ∑ s, ∑ s', x s * x s' * P s s' ≤ q} =
      ((stdGaussianPi ι).map (F *ᵥ ·)).real {x | ∑ s, ∑ s', x s * x s' * P s s' ≤ q / c} := by
  have hQc : Continuous fun x : ι → ℝ ↦ ∑ s, ∑ s', x s * x s' * P s s' :=
    continuous_finset_sum _ fun s _ ↦ continuous_finset_sum _ fun s' _ ↦
      ((continuous_apply s).mul (continuous_apply s')).mul continuous_const
  have hm : ∀ G : Matrix ι ι ℝ, Measurable (G *ᵥ · : (ι → ℝ) → ι → ℝ) := fun G ↦
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  rw [map_measureReal_apply (hm _) (measurableSet_le hQc.measurable measurable_const),
    map_measureReal_apply (hm _) (measurableSet_le hQc.measurable measurable_const)]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_setOf_eq, smul_mulVec, Pi.smul_apply, smul_eq_mul]
  have hc2 : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have e : ∑ s, ∑ s', Real.sqrt c * (F *ᵥ z) s * (Real.sqrt c * (F *ᵥ z) s') * P s s' =
      c * ∑ s, ∑ s', (F *ᵥ z) s * (F *ᵥ z) s' * P s s' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ ↦ ?_
    linear_combination ((F *ᵥ z) s * (F *ᵥ z) s' * P s s') * hc2
  rw [e, le_div_iff₀ hc, mul_comm]

theorem entryMax_smul_le (a : ℝ) (X : Matrix ι ι ℝ) :
    entryMax (a • X) ≤ |a| * entryMax X :=
  Real.iSup_le (fun p ↦ by
      rw [smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le_entryMax X p.1 p.2) (abs_nonneg a))
    (mul_nonneg (abs_nonneg a) (entryMax_nonneg X))

/-- **Lipschitz dependence of a Gaussian ellipsoid mass on the threshold scale, uniform in
`q`.** If `Λ = F Fᵀ` satisfies `v₀ ‖u‖² ≤ uᵀΛu` (sup norm, `v₀ > 0`) and `{xᵀPx ≤ q}` is convex,
then for every `c ≥ 1/2`,
`|N(0,Λ){xᵀPx ≤ q/c} − N(0,Λ){xᵀPx ≤ q}| ≤ 2 gaussCmpConst / v₀ · entryMax Λ · |c − 1|`. -/
theorem abs_map_mulVec_real_quadForm_div_sub_le (F P : Matrix ι ι ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hF : ∀ u : ι → ℝ, v₀ * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((F * Fᵀ) *ᵥ u)) (q : ℝ)
    (hK : Convex ℝ {x : ι → ℝ | ∑ s, ∑ s', x s * x s' * P s s' ≤ q}) {c : ℝ} (hc : 1 / 2 ≤ c) :
    |((stdGaussianPi ι).map (F *ᵥ ·)).real {x | ∑ s, ∑ s', x s * x s' * P s s' ≤ q / c} -
        ((stdGaussianPi ι).map (F *ᵥ ·)).real {x | ∑ s, ∑ s', x s * x s' * P s s' ≤ q}| ≤
      2 * gaussCmpConst ι / v₀ * entryMax (F * Fᵀ) * |c - 1| := by
  have hc0 : 0 < c := by linarith
  rw [← map_smul_mulVec_real_quadForm_le F P hc0 q]
  have hcov : (Real.sqrt c • F) * (Real.sqrt c • F)ᵀ = c • (F * Fᵀ) := by
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hc0.le]
  have hv2 : 0 < v₀ / 2 := by positivity
  have h₂ : ∀ u : ι → ℝ, v₀ / 2 * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((F * Fᵀ) *ᵥ u) := fun u ↦ by
    have := hF u
    nlinarith [sq_nonneg ‖u‖]
  have h₁ : ∀ u : ι → ℝ, v₀ / 2 * ‖u‖ ^ 2 ≤
      u ⬝ᵥ (((Real.sqrt c • F) * (Real.sqrt c • F)ᵀ) *ᵥ u) := fun u ↦ by
    rw [hcov, smul_mulVec, dotProduct_smul, smul_eq_mul]
    have := hF u
    have hn : 0 ≤ v₀ * ‖u‖ ^ 2 := by positivity
    nlinarith
  have hcmp := abs_real_convex_gaussian_sub_le (Real.sqrt c • F) F hv2 h₁ h₂ hK
  rw [hcov] at hcmp
  have hdiff : c • (F * Fᵀ) - F * Fᵀ = (c - 1) • (F * Fᵀ) := by rw [sub_smul, one_smul]
  rw [hdiff] at hcmp
  have hE := entryMax_smul_le (c - 1) (F * Fᵀ)
  have hG : 0 ≤ gaussCmpConst ι / (v₀ / 2) := div_nonneg gaussCmpConst_nonneg hv2.le
  calc _ ≤ gaussCmpConst ι / (v₀ / 2) * entryMax ((c - 1) • (F * Fᵀ)) := hcmp
    _ ≤ gaussCmpConst ι / (v₀ / 2) * (|c - 1| * entryMax (F * Fᵀ)) :=
        mul_le_mul_of_nonneg_left hE hG
    _ = 2 * gaussCmpConst ι / v₀ * entryMax (F * Fᵀ) * |c - 1| := by
        field_simp

end Scaling

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-- **The `χ²(S)` cdf under threshold scaling, uniform in `q`.** For full-support `μ` and
`Γ_true ≻ 0` there is `K_g ≥ 0` such that for every real `q` and every `c ≥ 1/2`,
`|F_{χ²(S)}(q/c) − F_{χ²(S)}(q)| ≤ K_g |c − 1|`. -/
theorem exists_abs_cdf_chiSquared_div_sub_le [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ q c : ℝ, 1 / 2 ≤ c →
      |cdf (chiSquared (Fintype.card State)) (q / c) -
          cdf (chiSquared (Fintype.card State)) q| ≤ Kg * |c - 1| := by
  have hA : IsUnit (tdA M π μ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ
      (μmin := Finset.univ.inf' Finset.univ_nonempty μ.prob)
      ((Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s) (fun s ↦ Finset.inf'_le _ (mem_univ s)))
  set F := gaussCovFactor (tdA M π μ) (trueGamma M π μ) with hFdef
  have hFF : F * Fᵀ = trueLambda M π μ :=
    gaussCovFactor_mul_transpose (tdA M π μ) fun s ↦ (hΓ s).le
  set g := diagMin (trueGamma M π μ) with hg
  have hg0 : 0 < g := (Finset.lt_inf'_iff _).2 fun s _ ↦ hΓ s
  have hgle : ∀ r, g ≤ trueGamma M π μ r := fun r ↦ Finset.inf'_le _ (mem_univ r)
  set v₀ := g / ((Fintype.card State : ℝ) * (∑ r, ∑ s, |tdA M π μ r s|) ^ 2 + 1) with hv₀
  have hv₀0 : 0 < v₀ := by positivity
  have hF : ∀ u : State → ℝ, v₀ * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((F * Fᵀ) *ᵥ u) := fun u ↦ by
    rw [hFF]
    exact quadForm_target_ge (tdA M π μ) hA (trueGamma M π μ) hg0.le hgle u
  refine ⟨2 * gaussCmpConst State / v₀ * entryMax (F * Fᵀ),
    mul_nonneg (div_nonneg (mul_nonneg zero_le_two gaussCmpConst_nonneg) hv₀0.le)
      (entryMax_nonneg _), fun q c hc ↦ ?_⟩
  have h := abs_map_mulVec_real_quadForm_div_sub_le F (trueLambda M π μ)⁻¹ hv₀0 hF q
    (convex_trueLambda_ellipsoid M π μ hμ hΓ q) hc
  rw [← gaussCov_eq_map_mulVec, gaussCov_ellipsoid_eq_chiSquared M π μ hμ hΓ,
    gaussCov_ellipsoid_eq_chiSquared M π μ hμ hΓ] at h
  exact h

/-- `t = T^{-1/3}` satisfies `0 < t ≤ 1` and `t³ T = 1` for `T ≥ 1`. -/
theorem rpow_neg_third_facts {T : ℕ} (hT : 1 ≤ T) :
    0 < (T : ℝ) ^ (-(1 / 3 : ℝ)) ∧ (T : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 ∧
      ((T : ℝ) ^ (-(1 / 3 : ℝ))) ^ 3 * T = 1 := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  refine ⟨Real.rpow_pos_of_pos hT0 _, Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num), ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
  norm_num
  rw [Real.rpow_neg_one, inv_mul_cancel₀ hT0.ne']

/-! ## The plug-in ellipsoid at rate `T^{-1/3}` -/

/-- **Plug-in confidence ellipsoid at the finite-`T` rate `T^{-1/3}` (corrected C47(3)).**
For full-support `μ`, `0 < η₀ ≤ 1`, every `V₀` and `Γ_true ≻ 0`, with the printed plug-in
covariance `Λ̂_T = Ā_T⁻¹ Γ̂_T Ā_T⁻ᵀ` (`lambdaHat`; Lean's junk inverse on the singular event,
C47(4)), the Polyak–Ruppert average `V̄_T` and `S = |State|`, there is an instance constant
`K > 0` (depending on `M, π, μ, η₀, V₀` only; independent of `T` and `q`) such that for every
`T ≥ 1` and every real `q`,
`|P(T (V^π − V̄_T)ᵀ Λ̂_T⁻¹ (V^π − V̄_T) ≤ q) − F_{χ²(S)}(q)| ≤ K T^{-1/3}`.
Source: `inference.tex:207–213`, plug-in `Λ̂_T` `eq:defn-hat-Lambda` `inference.tex:180–182`;
C47(3) (threshold `q`, not `q²`; `√T` applied once), C43 (limit covariance
`A⁻¹ diag(Γ_true) A⁻ᵀ`). Instance constant, not a printed coefficient. -/
theorem exists_coverage_ellipsoid_plugin_rate [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ q : ℝ,
      |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
            (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
              (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                (lambdaHat M η₀ V₀ ω')⁻¹ s s' ≤ q}.indicator 1 ω -
        cdf (chiSquared (Fintype.card State)) q| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨K₀, hK₀, hor⟩ := abs_lawProb_convex_sub_gaussCov_le_third_sharp M π μ h0 h1 V₀ hμ hΓ
  obtain ⟨C, hC, hBad⟩ := exists_pathProb_lambdaHat_inv_sub_gt_le M π μ hμ h0 h1 V₀ hΓ
  obtain ⟨Ce, hCe, hCx⟩ := exists_sum_abs_sq_le_mul_quadForm_trueLambda_inv M π μ hμ hΓ
  obtain ⟨Kg, hKg, hGs⟩ := exists_abs_cdf_chiSquared_div_sub_le M π μ hμ hΓ
  set Fc := cdf (chiSquared (Fintype.card State)) with hFdef
  set L : Matrix State State ℝ := (trueLambda M π μ)⁻¹ with hLdef
  set Q : (State → ℝ) → ℝ := fun x ↦ ∑ s, ∑ s', x s * x s' * L s s' with hQdef
  refine ⟨K₀ + C + Kg * Ce + 2 * Ce, by positivity, fun T hT q ↦ ?_⟩
  obtain ⟨ht0, ht1, ht3⟩ := rpow_neg_third_facts hT
  set t := (T : ℝ) ^ (-(1 / 3 : ℝ)) with htdef
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  -- the coverage probability as a path event of `√TΔ̄_T`
  have hE : ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
          (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
            (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
              (lambdaHat M η₀ V₀ ω')⁻¹ s s' ≤ q}.indicator 1 ω =
      pathProb M π μ T {ω | ∑ s, ∑ s', scaledError M π η₀ V₀ ω s *
        scaledError M π η₀ V₀ ω s' * (lambdaHat M η₀ V₀ ω)⁻¹ s s' ≤ q} := by
    unfold pathProb
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    congr 1
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply,
      natCast_mul_quadForm_eq_scaledError]
  rw [hE]
  set E : Set (Fin T → Tuple State Action) := {ω | ∑ s, ∑ s', scaledError M π η₀ V₀ ω s *
    scaledError M π η₀ V₀ ω s' * (lambdaHat M η₀ V₀ ω)⁻¹ s s' ≤ q} with hEdef
  have hPE0 : 0 ≤ pathProb M π μ T E := pathProb_nonneg M π μ T _
  have hPE1 : pathProb M π μ T E ≤ 1 :=
    (pathProb_mono M π μ T (Set.subset_univ _)).trans (le_of_eq (pathProb_univ M π μ T))
  have hF0 : 0 ≤ Fc q := cdf_nonneg _ q
  have hF1 : Fc q ≤ 1 := cdf_le_one _ q
  have hKgCe : 0 ≤ Kg * Ce * t := by positivity
  have hKt : (K₀ + C + Kg * Ce + 2 * Ce) * t = K₀ * t + C * t + Kg * Ce * t + 2 * Ce * t := by
    ring
  rw [hKt]
  have hK₀t : 0 ≤ K₀ * t := by positivity
  have hCt : 0 ≤ C * t := by positivity
  set κ := Ce * t with hκdef
  by_cases hκ : κ ≤ 1 / 2
  swap
  · -- trivial regime: `1 < 2κ`
    push_neg at hκ
    have h2κ : 2 * Ce * t = 2 * κ := by rw [hκdef]; ring
    rw [abs_le]
    constructor <;> linarith
  -- the bad event
  set B : Set (Fin T → Tuple State Action) :=
    {ω | ∃ s s', t < |(lambdaHat M η₀ V₀ ω)⁻¹ s s' - (trueLambda M π μ)⁻¹ s s'|} with hBdef
  have hPB : pathProb M π μ T B ≤ C * t := by
    refine (hBad T hT t ht0 ht1).trans (le_of_eq ?_)
    rw [div_eq_iff (by positivity)]
    linear_combination (-C) * ht3
  have hB0 : 0 ≤ pathProb M π μ T B := pathProb_nonneg M π μ T _
  -- off the bad event the plug-in form is within relative error `κ` of the oracle form
  have key : ∀ ω, ω ∉ B → ∀ x : State → ℝ,
      |∑ s, ∑ s', x s * x s' * (lambdaHat M η₀ V₀ ω)⁻¹ s s' - Q x| ≤ κ * Q x := by
    intro ω hω x
    simp only [hBdef, Set.mem_setOf_eq, not_exists, not_lt] at hω
    have h1' := abs_quadForm_sub_le x _ _ hω
    obtain ⟨-, hx⟩ := hCx x
    calc _ ≤ (∑ s, |x s|) ^ 2 * t := h1'
      _ ≤ Ce * Q x * t := mul_le_mul_of_nonneg_right hx ht0.le
      _ = κ * Q x := by rw [hκdef]; ring
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1' : 0 < 1 - κ := by linarith
  have hκ2 : 0 < 1 + κ := by linarith
  set Hp : Set (Fin T → Tuple State Action) :=
    {ω | Q (scaledError M π η₀ V₀ ω) ≤ q / (1 - κ)} with hHpdef
  set Hm : Set (Fin T → Tuple State Action) :=
    {ω | Q (scaledError M π η₀ V₀ ω) ≤ q / (1 + κ)} with hHmdef
  have hsub1 : E ⊆ Hp ∪ B := by
    intro ω hω
    by_cases hb' : ω ∈ B
    · exact Or.inr hb'
    · left
      have hk := abs_le.1 (key ω hb' (scaledError M π η₀ V₀ ω))
      simp only [hEdef, hHpdef, Set.mem_setOf_eq] at hω ⊢
      rw [le_div_iff₀ hκ1']
      nlinarith [hk.1]
  have hsub2 : Hm ⊆ E ∪ B := by
    intro ω hω
    by_cases hb' : ω ∈ B
    · exact Or.inr hb'
    · left
      have hk := abs_le.1 (key ω hb' (scaledError M π η₀ V₀ ω))
      simp only [hEdef, hHmdef, Set.mem_setOf_eq] at hω ⊢
      rw [le_div_iff₀ hκ2] at hω
      nlinarith [hk.2]
  have hup : pathProb M π μ T E ≤ pathProb M π μ T Hp + pathProb M π μ T B :=
    (pathProb_mono M π μ T hsub1).trans (pathProb_union_le M π μ T _ _)
  have hlo : pathProb M π μ T Hm ≤ pathProb M π μ T E + pathProb M π μ T B :=
    (pathProb_mono M π μ T hsub2).trans (pathProb_union_le M π μ T _ _)
  -- oracle ellipsoid probabilities at arbitrary thresholds (sharp rate)
  have hH : ∀ c : ℝ, |pathProb M π μ T {ω | Q (scaledError M π η₀ V₀ ω) ≤ c} - Fc c| ≤
      K₀ * t := by
    intro c
    have h := hor T hT {x | Q x ≤ c} (convex_trueLambda_ellipsoid M π μ hμ hΓ c)
    rw [gaussCov_ellipsoid_eq_chiSquared M π μ hμ hΓ c] at h
    exact h
  have hHp := abs_le.1 (hH (q / (1 - κ)))
  have hHm := abs_le.1 (hH (q / (1 + κ)))
  -- Gaussian side, uniform in `q`
  have hGp := abs_le.1 (hGs q (1 - κ) (by linarith))
  have hGm := abs_le.1 (hGs q (1 + κ) (by linarith))
  rw [show |1 - κ - 1| = κ by rw [show 1 - κ - 1 = -κ by ring, abs_neg, abs_of_nonneg hκ0]]
    at hGp
  rw [show |1 + κ - 1| = κ by rw [show 1 + κ - 1 = κ by ring, abs_of_nonneg hκ0]] at hGm
  have hKgκ : Kg * κ = Kg * Ce * t := by rw [hκdef]; ring
  have h2 : 0 ≤ 2 * Ce * t := by positivity
  rw [abs_le]
  constructor <;> linarith [hHp.1, hHp.2, hHm.1, hHm.2, hGp.1, hGp.2, hGm.1, hGm.2]

/-- **Plug-in confidence ellipsoid at the printed `χ²(S)` quantile, finite-`T` rate `T^{-1/3}`
(corrected C47(3)).** Same hypotheses as `exists_coverage_ellipsoid_plugin_rate`. There is an
instance constant `K > 0` (depending on `M, π, μ, η₀, V₀` only; independent of `T`, `α` and `R`)
such that for every `α ∈ (0,1)`, every `1 − α` quantile `R` of `χ²(S)` (`F_{χ²(S)}(R) = 1 − α`;
one exists by `exists_chiSquared_quantile`) and every `T ≥ 1`,
`|P(T (V^π − V̄_T)ᵀ Λ̂_T⁻¹ (V^π − V̄_T) ≤ R) − (1 − α)| ≤ K T^{-1/3}`, with the printed plug-in
`Λ̂_T`. Source: `inference.tex:207–213`; corrected threshold `R` (not `R²`) and scaling per
C47(3); C43, C47(4). Instance constant, not a printed coefficient. -/
theorem exists_coverage_ellipsoid_plugin_chiSquared_rate [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α < 1 → ∀ R : ℝ,
      cdf (chiSquared (Fintype.card State)) R = 1 - α → ∀ T : ℕ, 1 ≤ T →
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
              (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
                (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                  (lambdaHat M η₀ V₀ ω')⁻¹ s s' ≤ R}.indicator 1 ω - (1 - α)| ≤
          K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := exists_coverage_ellipsoid_plugin_rate M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K, hK, fun α _ _ R hR T hT ↦ ?_⟩
  rw [← hR]
  exact hb T hT R

end StatisticalRL.Ch7Rest.TDInference

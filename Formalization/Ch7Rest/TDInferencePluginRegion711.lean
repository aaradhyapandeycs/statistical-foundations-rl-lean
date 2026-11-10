import Formalization.Ch7Rest.TDInferenceConfChiSq711
import Formalization.Ch7Rest.TDInferencePluginCoverage711

/-!
# Plug-in-covariance confidence ellipsoid: asymptotic `χ²(S)` coverage (corrected C47(3))

Source: `chapters/inference.tex:198–213` (the confidence regions built from `eq:convex.Cdelta`:
rectangles :198–205, ellipsoids :207–213, "`R` is the `1 − α` quantile of the `χ²(d)`
distribution"), the plug-in covariance `eq:defn-hat-Lambda` (`inference.tex:180–182`), and
`docs/SOURCE-ISSUES.md` C47(2), C47(3), C47(4), C43.

With the **printed plug-in covariance** `Λ̂_T = Ā_T⁻¹ Γ̂_T Ā_T⁻ᵀ` (`lambdaHat`), the
Polyak–Ruppert average `V̄_T` (`prAverage`) and `S = |State|`:

* `tendsto_coverage_ellipsoid_plugin`: for every real `q`,
  `P(T (V^π − V̄_T)ᵀ Λ̂_T⁻¹ (V^π − V̄_T) ≤ q) → F_{χ²(S)}(q)` as `T → ∞`;
* `tendsto_coverage_ellipsoid_plugin_chiSquared`: for every `α ∈ (0,1)` and every `1 − α`
  quantile `R` of `χ²(S)` (one exists, `exists_chiSquared_quantile`),
  `P(T (V^π − V̄_T)ᵀ Λ̂_T⁻¹ (V^π − V̄_T) ≤ R) → 1 − α`.

Hypotheses: full-support `μ`, `0 < η₀ ≤ 1` (containing the printed `(0, 1/4)`), every `V₀`,
`Γ_true ≻ 0` (added non-degeneracy hypothesis). By C43 the limit covariance of `Λ̂_T` is the
corrected `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (`trueLambda`).

**Corrected shape, not the printed formula (C47(3)).** The threshold of the quadratic form is the
quantile `R` itself (not `R²`), and the scaling is `T (V^π − V̄_T)ᵀ Λ̂_T⁻¹ (V^π − V̄_T)`
(the `√T` scaling applied once, to the deviation).

**Asymptotic only.** The plug-in consistency `eq_defn_hat_Lambda_corrected` has no rate, so the
result is a limit, not a finite-`T` bound; no rate is claimed. The limit is pointwise in `q`.

**Route.** On the good event `{∀ s s', |Λ̂_T(s,s') − Λ(s,s')| ≤ δ}` (probability `→ 1`), the
continuity of matrix inversion at the invertible `Λ` makes `Λ̂_T⁻¹` entrywise `κ/C`-close to
`Λ⁻¹`, and `(∑_s |x_s|)² ≤ C xᵀΛ⁻¹x` turns this into
`(1 − κ) xᵀΛ⁻¹x ≤ xᵀΛ̂_T⁻¹x ≤ (1 + κ) xᵀΛ⁻¹x`. The plug-in ellipsoid event is then sandwiched
between the oracle ellipsoid events at thresholds `q/(1 + κ)` and `q/(1 − κ)`, whose
probabilities are within `K₀ T^{-1/3} log(2T)` of `F_{χ²(S)}` there
(`abs_lawProb_convex_sub_gaussCov_le_third_log`, `gaussCov_ellipsoid_eq_chiSquared`); the
continuity of the `χ²(S)` cdf closes the argument.

**Junk value (C47(4)).** When some state is unsampled, `Ā_T` is singular, the printed `Λ̂_T` is
undefined and Lean's `Matrix.inv` returns `0` (so `Λ̂_T = 0` and `Λ̂_T⁻¹ = 0`). No special handling
is needed: such outcomes have `Λ̂_T` entrywise far from `Λ` (`diag Λ ≻ 0`), hence lie in the bad
event whose probability tends to `0`, so the limit does not depend on the junk value.

Not covered here: the plug-in `ℓ∞` rectangle (C47(2)) with a random level computed from
`N(0, Λ̂_T)`, data-selected convex sets (C47(1)), and any rate for the plug-in rule.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability

/-! ## Generic helpers -/

/-- The `χ²(k)` cdf is continuous for `k ≥ 1` (`χ²(k)` has a density, so no atoms). -/
theorem continuous_cdf_chiSquared {k : ℕ} (hk : 0 < k) : Continuous (cdf (chiSquared k)) := by
  haveI := isProbabilityMeasure_chiSquared hk
  have hac : chiSquared k ≪ volume := withDensity_absolutelyContinuous _ _
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  have hsing : (cdf (chiSquared k)).measure {a} = 0 := by
    rw [measure_cdf]
    exact hac Real.volume_singleton
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hsing
  rw [(cdf (chiSquared k)).mono.continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  exact le_antisymm ((cdf (chiSquared k)).mono.leftLim_le le_rfl) (by linarith)

/-- `T^{-1/3} log(2T) → 0`, times any constant. -/
theorem tendsto_const_mul_rpow_neg_third_mul_log (K : ℝ) :
    Tendsto (fun T : ℕ ↦ K * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T))) atTop (𝓝 0) := by
  have h3 : (0 : ℝ) < 1 / 3 := by norm_num
  have hA : Tendsto (fun x : ℝ ↦ Real.log 2 * x ^ (-(1 / 3 : ℝ)) +
      Real.log x / x ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop h3).const_mul (Real.log 2)
    have h2 := (isLittleO_log_rpow_atTop h3).tendsto_div_nhds_zero
    simpa using h1.add h2
  have hB : Tendsto (fun x : ℝ ↦ x ^ (-(1 / 3 : ℝ)) * Real.log (2 * x)) atTop (𝓝 0) := by
    refine hA.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.log_mul (by norm_num) hx.ne', Real.rpow_neg hx.le, div_eq_mul_inv]
    ring
  simpa using (hB.comp tendsto_natCast_atTop_atTop).const_mul K

/-- **Entrywise continuity of matrix inversion at an invertible matrix.** -/
theorem exists_inv_entry_close {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Matrix ι ι ℝ)
    (hL : IsUnit L.det) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ L' : Matrix ι ι ℝ, (∀ i j, |L' i j - L i j| ≤ δ) →
      ∀ i j, |L'⁻¹ i j - L⁻¹ i j| ≤ ε := by
  have hc : ContinuousAt Inv.inv L := continuousAt_matrix_inv L (by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.1 hL))
  have hev : ∀ᶠ L' in 𝓝 L, ∀ i j, |L'⁻¹ i j - L⁻¹ i j| < ε := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hcij : ContinuousAt (fun L' : Matrix ι ι ℝ ↦ L'⁻¹ i j) L :=
      (continuous_id.matrix_elem i j).continuousAt.comp hc
    filter_upwards [hcij.eventually (Metric.ball_mem_nhds _ hε)] with L' hL'
    rwa [Real.dist_eq] at hL'
  have hev' : ∀ᶠ L' : ι → ι → ℝ in 𝓝 (fun i j ↦ L i j),
      ∀ i j, |(Matrix.of L')⁻¹ i j - L⁻¹ i j| < ε := hev
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev'
  refine ⟨δ / 2, by positivity, fun L' hL' i j ↦ (hball ?_ i j).le⟩
  refine lt_of_le_of_lt ((dist_pi_le_iff (by positivity)).2 fun i ↦
    (dist_pi_le_iff (by positivity)).2 fun j ↦ ?_) (by linarith : δ / 2 < δ)
  rw [Real.dist_eq]
  exact hL' i j

/-- **`ℓ¹`-norm squared is dominated by a nondegenerate weighted sum of squares.** If `B` is
invertible and `c > 0`, then some `C > 0` has `(∑_s |x_s|)² ≤ C ∑_r (∑_s x_s B_{rs})² c_r`. -/
theorem exists_sum_abs_sq_le_mul_sumSq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B : Matrix ι ι ℝ) (hB : IsUnit B.det) (c : ι → ℝ) (hc : ∀ r, 0 < c r) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ι → ℝ,
      (∑ s, |x s|) ^ 2 ≤ C * ∑ r, (∑ s, x s * B r s) ^ 2 * c r := by
  set cmin : ℝ := Finset.univ.inf' Finset.univ_nonempty c with hcmin
  have hcmin0 : 0 < cmin := (Finset.lt_inf'_iff _).2 fun r _ ↦ hc r
  have hcminle : ∀ r, cmin ≤ c r := fun r ↦ Finset.inf'_le _ (mem_univ r)
  set β : ℝ := ∑ s, ∑ r, |B⁻¹ s r| with hβ
  have hβ0 : 0 ≤ β := by positivity
  refine ⟨β ^ 2 * Fintype.card ι / cmin + 1, by positivity, fun x ↦ ?_⟩
  set y : ι → ℝ := fun r ↦ ∑ s, x s * B r s with hy
  have hxy : ∀ s, x s = ∑ r, B⁻¹ s r * y r := by
    intro s
    have h : (B⁻¹ * B) *ᵥ x = x := by rw [nonsing_inv_mul B hB, one_mulVec]
    rw [← mulVec_mulVec] at h
    have hs := congrFun h s
    rw [← hs]
    simp only [mulVec, dotProduct, hy]
    refine sum_congr rfl fun r _ ↦ ?_
    congr 1
    exact sum_congr rfl fun s' _ ↦ mul_comm _ _
  set Y : ℝ := ∑ r, |y r| with hY
  have hY0 : 0 ≤ Y := by positivity
  have hx1 : ∑ s, |x s| ≤ β * Y := by
    rw [hβ, Finset.sum_mul]
    refine sum_le_sum fun s _ ↦ ?_
    rw [hxy s, Finset.sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ ↦ ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (single_le_sum (f := fun r ↦ |y r|)
      (fun _ _ ↦ abs_nonneg _) (mem_univ r)) (abs_nonneg _)
  have hY2 : Y ^ 2 ≤ Fintype.card ι * ∑ r, y r ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun r ↦ |y r|)
    simp only [sq_abs, Finset.card_univ] at h
    exact h
  have hyc : ∑ r, y r ^ 2 ≤ (∑ r, y r ^ 2 * c r) / cmin := by
    rw [le_div_iff₀ hcmin0, Finset.sum_mul]
    exact sum_le_sum fun r _ ↦ mul_le_mul_of_nonneg_left (hcminle r) (sq_nonneg _)
  have hQ0 : 0 ≤ ∑ r, y r ^ 2 * c r :=
    sum_nonneg fun r _ ↦ mul_nonneg (sq_nonneg _) (hc r).le
  have hsx : 0 ≤ ∑ s, |x s| := by positivity
  calc (∑ s, |x s|) ^ 2 ≤ (β * Y) ^ 2 := pow_le_pow_left₀ hsx hx1 2
    _ = β ^ 2 * Y ^ 2 := by ring
    _ ≤ β ^ 2 * (Fintype.card ι * ((∑ r, y r ^ 2 * c r) / cmin)) := by
        gcongr
        exact hY2.trans (mul_le_mul_of_nonneg_left hyc (Nat.cast_nonneg _))
    _ = β ^ 2 * Fintype.card ι / cmin * ∑ r, y r ^ 2 * c r := by ring
    _ ≤ (β ^ 2 * Fintype.card ι / cmin + 1) * ∑ r, y r ^ 2 * c r := by nlinarith

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-- `T (V^π − V̄_T)ᵀ L (V^π − V̄_T) = (√TΔ̄_T)ᵀ L (√TΔ̄_T)` for any matrix `L`. -/
theorem natCast_mul_quadForm_eq_scaledError (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) (L : Matrix State State ℝ) :
    (T : ℝ) * ∑ s, ∑ s', (M.valueFixedPoint π s - prAverage M η₀ V₀ ω s) *
        (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω s') * L s s' =
      ∑ s, ∑ s', scaledError M π η₀ V₀ ω s * scaledError M π η₀ V₀ ω s' * L s s' := by
  have hT2 : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ ↦ ?_
  simp only [scaledError, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (-((M.valueFixedPoint π s - prAverage M η₀ V₀ ω s) *
    (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω s') * L s s')) * hT2

/-- The oracle quadratic form `xᵀΛ⁻¹x` dominates `(∑_s |x_s|)²` up to an instance constant, and
is nonnegative (`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`, `Γ_true ≻ 0`). -/
theorem exists_sum_abs_sq_le_mul_quadForm_trueLambda_inv [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : State → ℝ,
      0 ≤ ∑ s, ∑ s', x s * x s' * (trueLambda M π μ)⁻¹ s s' ∧
      (∑ s, |x s|) ^ 2 ≤ C * ∑ s, ∑ s', x s * x s' * (trueLambda M π μ)⁻¹ s s' := by
  have hA : IsUnit (tdA M π μ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ
      (μmin := Finset.univ.inf' Finset.univ_nonempty μ.prob)
      ((Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s) (fun s ↦ Finset.inf'_le _ (mem_univ s)))
  obtain ⟨C, hC, hCx⟩ := exists_sum_abs_sq_le_mul_sumSq (tdA M π μ) hA
    (fun r ↦ (trueGamma M π μ r)⁻¹) fun r ↦ inv_pos.2 (hΓ r)
  refine ⟨C, hC, fun x ↦ ?_⟩
  rw [quadForm_trueLambda_inv M π μ hμ hΓ x]
  exact ⟨sum_nonneg fun r _ ↦ mul_nonneg (sq_nonneg _) (inv_pos.2 (hΓ r)).le, hCx x⟩

/-! ## The plug-in ellipsoid -/

/-- **Asymptotic coverage of the plug-in confidence ellipsoid (corrected C47(3), asymptotic
only).** For full-support `μ`, `0 < η₀ ≤ 1`, every `V₀` and `Γ_true ≻ 0`, with the printed
plug-in covariance `Λ̂_T = Ā_T⁻¹ Γ̂_T Ā_T⁻ᵀ` (`lambdaHat`; Lean's junk inverse on the singular
event, C47(4)), the Polyak–Ruppert average `V̄_T` and `S = |State|`: for every real `q`,
`P(T (V^π − V̄_T)ᵀ Λ̂_T⁻¹ (V^π − V̄_T) ≤ q) → F_{χ²(S)}(q)` as `T → ∞`.
Source: `inference.tex:198–213`, plug-in `Λ̂_T` `eq:defn-hat-Lambda` `inference.tex:180–182`; C47(3)
(threshold `q`, not `q²`; `√T` applied once), C43 (limit covariance `A⁻¹ diag(Γ_true) A⁻ᵀ`). No rate. -/
theorem tendsto_coverage_ellipsoid_plugin [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) (q : ℝ) :
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
          (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
            (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
              (lambdaHat M η₀ V₀ ω')⁻¹ s s' ≤ q}.indicator 1 ω) atTop
      (𝓝 (cdf (chiSquared (Fintype.card State)) q)) := by
  classical
  obtain ⟨K₀, -, hb⟩ := abs_lawProb_convex_sub_gaussCov_le_third_log M π μ h0 h1 V₀ hμ hΓ
  obtain ⟨C, hC, hCx⟩ := exists_sum_abs_sq_le_mul_quadForm_trueLambda_inv M π μ hμ hΓ
  set F := cdf (chiSquared (Fintype.card State)) with hFdef
  have hFc : Continuous F := continuous_cdf_chiSquared Fintype.card_pos
  set L : Matrix State State ℝ := (trueLambda M π μ)⁻¹ with hLdef
  set Q : (State → ℝ) → ℝ := fun x ↦ ∑ s, ∑ s', x s * x s' * L s s' with hQdef
  have hLunit : IsUnit (trueLambda M π μ).det :=
    Matrix.isUnit_det_of_left_inverse (trueLambda_inv_mul M π μ hμ hΓ)
  -- the coverage probability as a path event of `√TΔ̄_T`
  have hE : ∀ T : ℕ, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
          (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
            (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
              (lambdaHat M η₀ V₀ ω')⁻¹ s s' ≤ q}.indicator 1 ω =
      pathProb M π μ T {ω | ∑ s, ∑ s', scaledError M π η₀ V₀ ω s *
        scaledError M π η₀ V₀ ω s' * (lambdaHat M η₀ V₀ ω)⁻¹ s s' ≤ q} := by
    intro T
    unfold pathProb
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    congr 1
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply,
      natCast_mul_quadForm_eq_scaledError]
  refine (tendsto_congr hE).2 ?_
  -- oracle ellipsoid probabilities at arbitrary thresholds
  have hH : ∀ T : ℕ, 1 ≤ T → ∀ c : ℝ,
      |pathProb M π μ T {ω | Q (scaledError M π η₀ V₀ ω) ≤ c} - F c| ≤
        K₀ * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)) := by
    intro T hT c
    have h := hb T hT {x | Q x ≤ c} (convex_trueLambda_ellipsoid M π μ hμ hΓ c)
    rw [gaussCov_ellipsoid_eq_chiSquared M π μ hμ hΓ c] at h
    exact h
  have hR := tendsto_const_mul_rpow_neg_third_mul_log K₀
  rw [Metric.tendsto_nhds]
  intro η hη
  -- choose the relative perturbation `κ`
  have hp : Tendsto (fun κ : ℝ ↦ F (q / (1 - κ))) (𝓝 0) (𝓝 (F q)) := by
    have hc : ContinuousAt (fun κ : ℝ ↦ q / (1 - κ)) 0 :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
    have := (hFc.continuousAt.comp hc).tendsto
    simpa using this
  have hm : Tendsto (fun κ : ℝ ↦ F (q / (1 + κ))) (𝓝 0) (𝓝 (F q)) := by
    have hc : ContinuousAt (fun κ : ℝ ↦ q / (1 + κ)) 0 :=
      continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num)
    have := (hFc.continuousAt.comp hc).tendsto
    simpa using this
  obtain ⟨κ, hκp, hκm, hκ0, hκ1⟩ :=
    (((hp.mono_left nhdsWithin_le_nhds).eventually
        (Metric.ball_mem_nhds _ (by positivity : (0 : ℝ) < η / 3))).and
      (((hm.mono_left nhdsWithin_le_nhds).eventually
        (Metric.ball_mem_nhds _ (by positivity : (0 : ℝ) < η / 3))).and
      (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)))).exists
  rw [Real.dist_eq] at hκp hκm
  obtain ⟨δ, hδ, hinv⟩ := exists_inv_entry_close (trueLambda M π μ) hLunit
    (by positivity : 0 < κ / C)
  let B : (T : ℕ) → Set (Fin T → Tuple State Action) := fun T ↦
    {ω | ∃ s s', δ < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|}
  have hB : Tendsto (fun T : ℕ ↦ pathProb M π μ T (B T)) atTop (𝓝 0) :=
    eq_defn_hat_Lambda_corrected State Action M π μ η₀ V₀ hμ h0 h1 δ hδ
  -- off the bad event the plug-in form is within relative error `κ` of the oracle form
  have key : ∀ (T : ℕ) (ω : Fin T → Tuple State Action), ω ∉ B T → ∀ x : State → ℝ,
      |∑ s, ∑ s', x s * x s' * (lambdaHat M η₀ V₀ ω)⁻¹ s s' - Q x| ≤ κ * Q x := by
    intro T ω hω x
    simp only [B, Set.mem_setOf_eq, not_exists, not_lt] at hω
    have hclose := hinv (lambdaHat M η₀ V₀ ω) hω
    have h1' := abs_quadForm_sub_le x _ _ hclose
    obtain ⟨-, hx⟩ := hCx x
    calc _ ≤ (∑ s, |x s|) ^ 2 * (κ / C) := h1'
      _ ≤ C * Q x * (κ / C) := mul_le_mul_of_nonneg_right hx (by positivity)
      _ = κ * Q x := by field_simp
  have hκ1' : 0 < 1 - κ := by linarith [hκ1]
  have hκ2 : 0 < 1 + κ := by linarith [hκ0]
  filter_upwards [eventually_ge_atTop 1,
    hB.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 3)),
    hR.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 3))] with T hT hBT hRT
  set E : Set (Fin T → Tuple State Action) := {ω | ∑ s, ∑ s', scaledError M π η₀ V₀ ω s *
    scaledError M π η₀ V₀ ω s' * (lambdaHat M η₀ V₀ ω)⁻¹ s s' ≤ q} with hEdef
  set Hp : Set (Fin T → Tuple State Action) :=
    {ω | Q (scaledError M π η₀ V₀ ω) ≤ q / (1 - κ)} with hHpdef
  set Hm : Set (Fin T → Tuple State Action) :=
    {ω | Q (scaledError M π η₀ V₀ ω) ≤ q / (1 + κ)} with hHmdef
  have hsub1 : E ⊆ Hp ∪ B T := by
    intro ω hω
    by_cases hb' : ω ∈ B T
    · exact Or.inr hb'
    · left
      have hk := abs_le.1 (key T ω hb' (scaledError M π η₀ V₀ ω))
      simp only [hEdef, hHpdef, Set.mem_setOf_eq] at hω ⊢
      rw [le_div_iff₀ hκ1']
      nlinarith [hk.1]
  have hsub2 : Hm ⊆ E ∪ B T := by
    intro ω hω
    by_cases hb' : ω ∈ B T
    · exact Or.inr hb'
    · left
      have hk := abs_le.1 (key T ω hb' (scaledError M π η₀ V₀ ω))
      simp only [hEdef, hHmdef, Set.mem_setOf_eq] at hω ⊢
      rw [le_div_iff₀ hκ2] at hω
      nlinarith [hk.2]
  have hup : pathProb M π μ T E ≤ pathProb M π μ T Hp + pathProb M π μ T (B T) :=
    (pathProb_mono M π μ T hsub1).trans (pathProb_union_le M π μ T _ _)
  have hlo : pathProb M π μ T Hm ≤ pathProb M π μ T E + pathProb M π μ T (B T) :=
    (pathProb_mono M π μ T hsub2).trans (pathProb_union_le M π μ T _ _)
  have hHp := abs_le.1 (hH T hT (q / (1 - κ)))
  have hHm := abs_le.1 (hH T hT (q / (1 + κ)))
  have hB0 : 0 ≤ pathProb M π μ T (B T) := pathProb_nonneg M π μ T _
  have a3 := abs_lt.1 hκp
  have a4 := abs_lt.1 hκm
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith [hHp.1, hHp.2, hHm.1, hHm.2, a3.1, a3.2, a4.1, a4.2]

/-- **Plug-in confidence ellipsoid at the printed `χ²(S)` quantile: asymptotic coverage
`1 − α` (corrected C47(3), asymptotic only).** Same hypotheses as
`tendsto_coverage_ellipsoid_plugin`. For every `α ∈ (0,1)` and every `1 − α` quantile `R` of
`χ²(S)` (`F_{χ²(S)}(R) = 1 − α`; one exists by `exists_chiSquared_quantile`),
`P(T (V^π − V̄_T)ᵀ Λ̂_T⁻¹ (V^π − V̄_T) ≤ R) → 1 − α`, with the printed plug-in `Λ̂_T`.
Source: `inference.tex:207–213`; corrected threshold `R` (not `R²`) and scaling per C47(3);
C43, C47(4). No rate. -/
theorem tendsto_coverage_ellipsoid_plugin_chiSquared [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) {α : ℝ} (_hα0 : 0 < α)
    (_hα1 : α < 1) {R : ℝ} (hR : cdf (chiSquared (Fintype.card State)) R = 1 - α) :
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
          (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
            (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
              (lambdaHat M η₀ V₀ ω')⁻¹ s s' ≤ R}.indicator 1 ω) atTop (𝓝 (1 - α)) := by
  rw [← hR]
  exact tendsto_coverage_ellipsoid_plugin M π μ h0 h1 V₀ hμ hΓ R

end StatisticalRL.Ch7Rest.TDInference

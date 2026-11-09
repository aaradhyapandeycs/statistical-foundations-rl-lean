import Formalization.Ch7Rest.TDInferencePluginCorrected711
import Formalization.Ch7Rest.TDInferenceConfInt711
import Formalization.Ch7Rest.TDInferenceC47Evidence711

/-!
# Plug-in-covariance coverage of fixed-shape confidence intervals (plan item D, C47 correction)

Source: `chapters/inference.tex:187–196` (the rule `eq:convex.Cdelta` :189–195, display :191–193,
and the claim that "such sets serve as approximate confidence regions" :196), the plug-in
covariance `eq:defn-hat-Lambda` :180–182, and SOURCE-ISSUES C47 ("Proposed correction"), C43.

With the plug-in `Λ̂_T = lambdaHat` (`TDInferencePlugin711.lean`) in place of the oracle
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ = trueLambda`, `q̂_T(u) = uᵀΛ̂_Tu`, `Φ(z) = N(0,1)(-∞, z]`:

* D1, one-sided (`tendsto_coverage_oneSided_plugin`): for `u ≠ 0` and `z ∈ ℝ`,
  `P(uᵀV̄_T − z√(q̂_T(u)/T) ≤ uᵀV^π) → Φ(z)`.
* D2, two-sided (`tendsto_coverage_twoSided_plugin`): for `u ≠ 0` and `z ≥ 0`,
  `P(|uᵀ(V̄_T − V^π)| ≤ z√(q̂_T(u)/T)) → 2Φ(z) − 1`.
* D3, Bonferroni box with plug-in diagonal (`eventually_coverage_rect_plugin_ge`): for `z ≥ 0`
  and every `η > 0`, eventually `P(∀ s, |V̄_T(s) − V^π(s)| ≤ z√(Λ̂_T(s,s)/T)) ≥ 1 − 2S(1 − Φ(z)) − η`.

Hypotheses: full-support `μ`, `0 < η₀ ≤ 1` (containing the printed `(0, 1/4)`), every `V₀`,
`Γ_true ≻ 0`. The direction `u` and the level `z` are fixed before the data (C47(1) does not
apply).

**Route.** On the good event `{∀ s s', |Λ̂_T(s,s') − Λ(s,s')| ≤ ε₁}` the random threshold
`z√q̂` is within `ε` of `z√q`, so the coverage event is sandwiched between two deterministic
half-spaces `{uᵀ√TΔ̄_T ≤ z√q ∓ ε}` up to the bad event. The half-space bound
(`exists_abs_lawProb_halfSpace_pivot_sub_le`, rate `K T^{-1/3}`, uniform in the threshold), the
continuity of `Φ` and the plug-in consistency `eq_defn_hat_Lambda_corrected` close the argument.

**Qualitative only.** The consistency result has no rate, so these are limits (asymptotic
coverage), not finite-`T` bounds. The limits are pointwise in `(u, z)`, not uniform.

**Hypothesis `Γ_true ≻ 0`.** This is an added non-degeneracy hypothesis: it gives `uᵀΛu > 0`
for `u ≠ 0` and is needed by the half-space result. Separately, by C43 the target covariance is
`A⁻¹ diag(Γ_true) A⁻ᵀ` (the limit of `Λ̂_T`), not the printed `Λ⋆`.

**Junk value (C47(4)).** On the event that some state is unsampled, `Ā_T` is singular and the
printed `Λ̂_T` is undefined; Lean's `Matrix.inv` returns 0 there, so `lambdaHat = 0` on that
event and the interval degenerates to the point estimate. No special handling is needed: the
proof charges every outcome with `Λ̂_T` entrywise `ε₁`-far from `Λ`, and since `diag Λ ≻ 0` under
`Γ_true ≻ 0` the singular event is contained in that bad event for small `ε₁`. Its probability
is at most `∑_s (1 − μ(s))^T → 0` (`pathProb_aBar_singular_le`), so the limits do not depend on
how the procedure is defined there.

Not covered: arbitrary or data-selected convex sets (C47(1)), the printed `ℓ∞`-quantile rectangle
(C47(2)), the ellipsoid (C47(3)), and any rate for the plug-in rule.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Probability.Stein StatisticalRL.Analysis

/-! ## Real-number helpers -/

/-- `|√a − √b| ≤ |a − b| / √b` for `b > 0` and any real `a` (`√a = 0` for `a < 0`). -/
theorem abs_sqrt_sub_sqrt_le_div (a : ℝ) {b : ℝ} (hb : 0 < b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| / Real.sqrt b := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  rw [le_div_iff₀ hsb]
  rcases le_or_gt 0 a with ha | ha
  · have h1 : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
      rw [show (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) =
          Real.sqrt a ^ 2 - Real.sqrt b ^ 2 by ring, Real.sq_sqrt ha, Real.sq_sqrt hb.le]
    have hsa := Real.sqrt_nonneg a
    rw [h1, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt a + Real.sqrt b)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  · rw [Real.sqrt_eq_zero'.2 ha.le, zero_sub, abs_neg, abs_of_pos hsb, Real.mul_self_sqrt hb.le,
      abs_of_neg (by linarith : a - b < 0)]
    linarith

variable {State : Type} [Fintype State]

/-- Entrywise closeness controls the quadratic form:
`|uᵀXu − uᵀYu| ≤ (∑ |u_s|)² ε₁` when every `|X(s,s') − Y(s,s')| ≤ ε₁`. -/
theorem abs_quadForm_sub_le (u : State → ℝ) (X Y : Matrix State State ℝ) {ε₁ : ℝ}
    (h : ∀ s s', |X s s' - Y s s'| ≤ ε₁) :
    |∑ s, ∑ s', u s * u s' * X s s' - ∑ s, ∑ s', u s * u s' * Y s s'| ≤
      (∑ s, |u s|) ^ 2 * ε₁ := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc |∑ s, ∑ s', (u s * u s' * X s s' - u s * u s' * Y s s')|
      ≤ ∑ s, ∑ s', |u s| * |u s'| * ε₁ := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ ↦
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s' _ ↦ ?_))
        rw [← mul_sub, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (h s s') (by positivity)
    _ = (∑ s, |u s|) ^ 2 * ε₁ := by
        rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
        exact sum_congr rfl fun s _ ↦ by rw [Finset.sum_mul]

variable {Action : Type} [Fintype Action] [DecidableEq State]

/-! ## Path-level facts -/

/-- A half-space event of `√TΔ̄_T` as a path event. -/
theorem pathProb_halfSpace_eq_lawProb (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) (u : State → ℝ) (c : ℝ) :
    pathProb M π μ T {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤ c} =
      lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ c} := rfl

omit [DecidableEq State] in
/-- `P(Eᶜ) = 1 − P(E)`. -/
theorem pathProb_compl (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (T : ℕ) (E : Set (Fin T → Tuple State Action)) :
    pathProb M π μ T Eᶜ = 1 - pathProb M π μ T E := by
  simp only [pathProb]
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine (sum_congr rfl fun ω _ ↦ ?_).trans (sum_pathWeight M π μ T)
  by_cases h : ω ∈ E <;> simp [h]

omit [DecidableEq State] in
/-- **Union bound, path form.** `P(∀ i, E_i) ≥ 1 − ∑_i (1 − P(E_i))`. -/
theorem one_sub_sum_le_pathProb_forall {ι : Type*} [Fintype ι] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (T : ℕ)
    (E : ι → Set (Fin T → Tuple State Action)) :
    1 - ∑ i, (1 - pathProb M π μ T (E i)) ≤ pathProb M π μ T {ω | ∀ i, ω ∈ E i} := by
  have hc : {ω | ∀ i, ω ∈ E i} = {ω | ∃ i, ω ∈ (E i)ᶜ}ᶜ := by
    ext ω; simp
  rw [hc, pathProb_compl]
  have h := pathProb_exists_le M π μ T fun i ↦ (E i)ᶜ
  simp only [pathProb_compl] at h
  linarith

/-! ## The sandwich: one-sided half-line with random threshold -/

/-- **Core sandwich.** For `u ≠ 0` and `z ∈ ℝ`,
`P(uᵀ√TΔ̄_T ≤ z√(uᵀΛ̂_Tu)) → Φ(z)`. -/
theorem tendsto_pathProb_le_mul_sqrt_quadForm_lambdaHat [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) {u : State → ℝ} (hu : u ≠ 0)
    (z : ℝ) :
    Tendsto (fun T : ℕ ↦ pathProb M π μ T {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤
        z * Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s')}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic z))) := by
  rw [gaussianReal_real_Iic]
  obtain ⟨K, hK, hb⟩ := exists_abs_lawProb_halfSpace_pivot_sub_le M π μ h0 h1 V₀ hμ hΓ
  set q : ℝ := ∑ s, ∑ s', u s * u s' * trueLambda M π μ s s' with hqdef
  have hq : 0 < q := quadForm_oracle_pos M π μ hμ hΓ hu
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  -- half-space probabilities at arbitrary thresholds
  have hH : ∀ T : ℕ, 1 ≤ T → ∀ c : ℝ,
      |pathProb M π μ T {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤ c} -
        stdCDF (c / Real.sqrt q)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
    intro T hT c
    have h : |lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ c / Real.sqrt q * Real.sqrt q} -
        (gaussianReal 0 1).real (Set.Iic (c / Real.sqrt q))| ≤
          K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := hb T hT u hu (c / Real.sqrt q)
    rw [div_mul_cancel₀ c hsq.ne', gaussianReal_real_Iic] at h
    rwa [pathProb_halfSpace_eq_lawProb]
  set U : ℝ := (∑ s, |u s|) ^ 2 with hUdef
  have hU : 0 ≤ U := by positivity
  have hR : Tendsto (fun T : ℕ ↦ K * (T : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).const_mul K
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 continuous_stdCDF z (η / 3) (by positivity)
  set ε : ℝ := δ * Real.sqrt q / 2 with hεdef
  have hε : 0 < ε := by positivity
  set ε₁ : ℝ := ε * Real.sqrt q / ((|z| + 1) * (U + 1)) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  let B : (T : ℕ) → Set (Fin T → Tuple State Action) := fun T ↦
    {ω | ∃ s s', ε₁ < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|}
  have hB : Tendsto (fun T : ℕ ↦ pathProb M π μ T (B T)) atTop (𝓝 0) :=
    eq_defn_hat_Lambda_corrected State Action M π μ η₀ V₀ hμ h0 h1 ε₁ hε₁
  -- off the bad event the random threshold is within `ε` of `z√q`
  have key : ∀ (T : ℕ) (ω : Fin T → Tuple State Action), ω ∉ B T →
      |z * Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s') -
        z * Real.sqrt q| ≤ ε := by
    intro T ω hω
    simp only [B, Set.mem_setOf_eq, not_exists, not_lt] at hω
    have h1' : |∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s' - q| ≤ U * ε₁ :=
      abs_quadForm_sub_le u _ _ hω
    have h2' := abs_sqrt_sub_sqrt_le_div (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s') hq
    have hz : 0 ≤ |z| := abs_nonneg z
    have hε₁eq : ε₁ * ((|z| + 1) * (U + 1)) = ε * Real.sqrt q := by
      simp only [hε₁def]; field_simp
    have hzU : |z| * U ≤ (|z| + 1) * (U + 1) := by nlinarith
    have h3 : |z| * (U * ε₁) ≤ ε * Real.sqrt q := by
      rw [← hε₁eq]; nlinarith
    rw [← mul_sub, abs_mul]
    calc |z| * |Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s') - Real.sqrt q|
        ≤ |z| * (|∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s' - q| / Real.sqrt q) :=
          mul_le_mul_of_nonneg_left h2' hz
      _ ≤ |z| * (U * ε₁ / Real.sqrt q) := by gcongr
      _ = |z| * (U * ε₁) / Real.sqrt q := by ring
      _ ≤ ε * Real.sqrt q / Real.sqrt q := by gcongr
      _ = ε := by field_simp
  have hplus : (z * Real.sqrt q + ε) / Real.sqrt q = z + δ / 2 := by
    simp only [hεdef]; field_simp
  have hminus : (z * Real.sqrt q - ε) / Real.sqrt q = z - δ / 2 := by
    simp only [hεdef]; field_simp
  have hΦp : |stdCDF (z + δ / 2) - stdCDF z| < η / 3 := by
    have := hcont (z + δ / 2) (by
      rw [Real.dist_eq, show z + δ / 2 - z = δ / 2 by ring, abs_of_pos (by positivity)]; linarith)
    rwa [Real.dist_eq] at this
  have hΦm : |stdCDF (z - δ / 2) - stdCDF z| < η / 3 := by
    have := hcont (z - δ / 2) (by
      rw [Real.dist_eq, show z - δ / 2 - z = -(δ / 2) by ring, abs_neg, abs_of_pos (by positivity)]
      linarith)
    rwa [Real.dist_eq] at this
  filter_upwards [eventually_ge_atTop 1, hB.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 3)),
    hR.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 3))] with T hT hBT hRT
  set E : Set (Fin T → Tuple State Action) := {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤
    z * Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s')} with hEdef
  set Hp : Set (Fin T → Tuple State Action) :=
    {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤ z * Real.sqrt q + ε} with hHpdef
  set Hm : Set (Fin T → Tuple State Action) :=
    {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤ z * Real.sqrt q - ε} with hHmdef
  have hsub1 : E ⊆ Hp ∪ B T := by
    intro ω hω
    by_cases hb' : ω ∈ B T
    · exact Or.inr hb'
    · left
      have := key T ω hb'
      simp only [hEdef, hHpdef, Set.mem_setOf_eq] at hω ⊢
      linarith [(abs_le.1 this).2]
  have hsub2 : Hm ⊆ E ∪ B T := by
    intro ω hω
    by_cases hb' : ω ∈ B T
    · exact Or.inr hb'
    · left
      have := key T ω hb'
      simp only [hEdef, hHmdef, Set.mem_setOf_eq] at hω ⊢
      linarith [(abs_le.1 this).1]
  have hup : pathProb M π μ T E ≤ pathProb M π μ T Hp + pathProb M π μ T (B T) :=
    (pathProb_mono M π μ T hsub1).trans (pathProb_union_le M π μ T _ _)
  have hlo : pathProb M π μ T Hm ≤ pathProb M π μ T E + pathProb M π μ T (B T) :=
    (pathProb_mono M π μ T hsub2).trans (pathProb_union_le M π μ T _ _)
  have hHp := hH T hT (z * Real.sqrt q + ε)
  have hHm := hH T hT (z * Real.sqrt q - ε)
  rw [hplus] at hHp
  rw [hminus] at hHm
  have hB0 : 0 ≤ pathProb M π μ T (B T) := pathProb_nonneg M π μ T _
  rw [Real.dist_eq, abs_sub_lt_iff]
  have a1 := abs_le.1 hHp
  have a2 := abs_le.1 hHm
  have a3 := abs_lt.1 hΦp
  have a4 := abs_lt.1 hΦm
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

/-! ## D1: one-sided -/

/-- The plug-in one-sided coverage probability as a path event of `√TΔ̄_T`. -/
theorem sum_pathWeight_oneSided_plugin_eq (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T) (u : State → ℝ) (z : ℝ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | ∑ s, u s * prAverage M η₀ V₀ ω' s -
          z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') / T) ≤
          ∑ s, u s * M.valueFixedPoint π s}.indicator 1 ω =
      pathProb M π μ T {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤
        z * Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s')} := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  simp only [pathProb]
  refine sum_congr rfl fun ω _ ↦ ?_
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, sum_mul_scaledError,
    sub_mul_sqrt_div_le_iff _ _ z _ _ hT']

/-- **D1, one-sided plug-in interval.** For every instance with full-support `μ`, `Γ_true ≻ 0`,
`0 < η₀ ≤ 1`, every `V₀`, `u ≠ 0` and `z ∈ ℝ`:
`P(uᵀV̄_T − z√(uᵀΛ̂_Tu/T) ≤ uᵀV^π) → Φ(z)`. -/
theorem tendsto_coverage_oneSided_plugin [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) {u : State → ℝ} (hu : u ≠ 0)
    (z : ℝ) :
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | ∑ s, u s * prAverage M η₀ V₀ ω' s -
          z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') / T) ≤
          ∑ s, u s * M.valueFixedPoint π s}.indicator 1 ω) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic z))) := by
  refine (tendsto_pathProb_le_mul_sqrt_quadForm_lambdaHat M π μ h0 h1 V₀ hμ hΓ hu z).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  exact (sum_pathWeight_oneSided_plugin_eq M π μ η₀ V₀ hT u z).symm

/-! ## D2: two-sided -/

/-- The plug-in two-sided coverage is `P(H(u)) + P(H(−u)) − 1` (random thresholds, `z ≥ 0`). -/
theorem sum_pathWeight_twoSided_plugin_eq (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T) (u : State → ℝ) {z : ℝ} (hz : 0 ≤ z) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action |
          |∑ s, u s * (prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s)| ≤
            z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') / T)}.indicator
          1 ω =
      pathProb M π μ T {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤
          z * Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s')} +
        pathProb M π μ T {ω | ∑ s, (-u) s * scaledError M π η₀ V₀ ω s ≤
          z * Real.sqrt (∑ s, ∑ s', (-u) s * (-u) s' * lambdaHat M η₀ V₀ ω s s')} - 1 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hpt : ∀ ω : Fin T → Tuple State Action,
      {ω' : Fin T → Tuple State Action |
          |∑ s, u s * (prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s)| ≤
            z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') / T)}.indicator
          1 ω =
        {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤
          z * Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s')}.indicator
            (fun _ ↦ (1 : ℝ)) ω +
        {ω | ∑ s, (-u) s * scaledError M π η₀ V₀ ω s ≤
          z * Real.sqrt (∑ s, ∑ s', (-u) s * (-u) s' * lambdaHat M η₀ V₀ ω s s')}.indicator
            (fun _ ↦ (1 : ℝ)) ω - 1 := by
    intro ω
    have he : ∑ s, u s * (prAverage M η₀ V₀ ω s - M.valueFixedPoint π s) =
        ∑ s, u s * prAverage M η₀ V₀ ω s - ∑ s, u s * M.valueFixedPoint π s := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun s _ ↦ by ring
    have hneg : ∑ s, (-u) s * scaledError M π η₀ V₀ ω s =
        -∑ s, u s * scaledError M π η₀ V₀ ω s := by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun s _ ↦ by simp
    have hqn : ∑ s, ∑ s', (-u) s * (-u) s' * lambdaHat M η₀ V₀ ω s s' =
        ∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s' := by
      simp
    have habs : |∑ s, u s * (prAverage M η₀ V₀ ω s - M.valueFixedPoint π s)| ≤
          z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s') / T) ↔
        |∑ s, u s * scaledError M π η₀ V₀ ω s| ≤
          z * Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s') := by
      rw [he, abs_le_mul_sqrt_div_iff _ z _ _ hT', sum_mul_scaledError]
    have hite := ite_abs_le_eq (w := ∑ s, u s * scaledError M π η₀ V₀ ω s)
      (mul_nonneg hz (Real.sqrt_nonneg
        (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s')))
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, hneg, hqn]
    rw [← hite]
    exact if_congr habs rfl rfl
  simp only [pathProb]
  rw [Finset.sum_congr rfl fun ω _ ↦ congrArg (pathWeight M π μ ω * ·) (hpt ω)]
  simp only [mul_sub, mul_add, mul_one, sum_sub_distrib, sum_add_distrib]
  rw [sum_pathWeight]

/-- **D2, two-sided plug-in interval.** Same hypotheses; for `u ≠ 0` and `z ≥ 0`:
`P(|uᵀ(V̄_T − V^π)| ≤ z√(uᵀΛ̂_Tu/T)) → 2Φ(z) − 1`. -/
theorem tendsto_coverage_twoSided_plugin [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) {u : State → ℝ} (hu : u ≠ 0)
    {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action |
          |∑ s, u s * (prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s)| ≤
            z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') / T)}.indicator
          1 ω) atTop
      (𝓝 (2 * (gaussianReal 0 1).real (Set.Iic z) - 1)) := by
  have hp := tendsto_pathProb_le_mul_sqrt_quadForm_lambdaHat M π μ h0 h1 V₀ hμ hΓ hu z
  have hm := tendsto_pathProb_le_mul_sqrt_quadForm_lambdaHat M π μ h0 h1 V₀ hμ hΓ
    (neg_ne_zero.2 hu) z
  have h := (hp.add hm).sub_const 1
  rw [← two_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  exact (sum_pathWeight_twoSided_plugin_eq M π μ η₀ V₀ hT u hz).symm

/-! ## D3: Bonferroni box with plug-in diagonal -/

/-- **D3, Bonferroni box with plug-in diagonal.** Same hypotheses; for `z ≥ 0` and every
`η > 0`, eventually
`P(∀ s, |V̄_T(s) − V^π(s)| ≤ z√(Λ̂_T(s,s)/T)) ≥ 1 − 2S(1 − Φ(z)) − η`. -/
theorem eventually_coverage_rect_plugin_ge [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) {z : ℝ} (hz : 0 ≤ z)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop,
      1 - 2 * (Fintype.card State : ℝ) * (1 - (gaussianReal 0 1).real (Set.Iic z)) - η ≤
        ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | ∀ s,
            |prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s| ≤
              z * Real.sqrt (lambdaHat M η₀ V₀ ω' s s / T)}.indicator 1 ω := by
  set Φz := (gaussianReal 0 1).real (Set.Iic z)
  -- coordinate events
  let F : (T : ℕ) → State → Set (Fin T → Tuple State Action) := fun T s ↦
    {ω' | |∑ s₁, (Pi.single s (1 : ℝ) : State → ℝ) s₁ *
        (prAverage M η₀ V₀ ω' s₁ - M.valueFixedPoint π s₁)| ≤
      z * Real.sqrt ((∑ a, ∑ b, (Pi.single s (1 : ℝ) : State → ℝ) a *
        (Pi.single s (1 : ℝ) : State → ℝ) b * lambdaHat M η₀ V₀ ω' a b) / T)}
  have hF : ∀ s, Tendsto (fun T : ℕ ↦ pathProb M π μ T (F T s)) atTop (𝓝 (2 * Φz - 1)) :=
    fun s ↦ tendsto_coverage_twoSided_plugin M π μ h0 h1 V₀ hμ hΓ (single_one_ne_zero s) hz
  have hlim : Tendsto (fun T : ℕ ↦ 1 - ∑ s, (1 - pathProb M π μ T (F T s))) atTop
      (𝓝 (1 - ∑ _s : State, (1 - (2 * Φz - 1)))) :=
    (tendsto_finset_sum _ fun s _ ↦ (hF s).const_sub 1).const_sub 1
  have hval : 1 - ∑ _s : State, (1 - (2 * Φz - 1)) =
      1 - 2 * (Fintype.card State : ℝ) * (1 - Φz) := by
    rw [sum_const, card_univ, nsmul_eq_mul]; ring
  rw [hval] at hlim
  filter_upwards [hlim.eventually (lt_mem_nhds (by linarith :
    1 - 2 * (Fintype.card State : ℝ) * (1 - Φz) - η <
      1 - 2 * (Fintype.card State : ℝ) * (1 - Φz)))] with T hT
  refine hT.le.trans ((one_sub_sum_le_pathProb_forall M π μ T (F T)).trans (le_of_eq ?_))
  simp only [pathProb]
  refine sum_congr rfl fun ω _ ↦ ?_
  congr 1
  simp only [F, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, sum_single_mul,
    quadForm_single]

/-! ## Combined export -/

/-- **Plug-in-covariance coverage (D1–D3).** For every instance with full-support `μ`,
`Γ_true ≻ 0`, `0 < η₀ ≤ 1` and every `V₀`:
(D1) for all `u ≠ 0`, `z ∈ ℝ`, `P(uᵀV̄_T − z√(uᵀΛ̂_Tu/T) ≤ uᵀV^π) → Φ(z)`;
(D2) for all `u ≠ 0`, `z ≥ 0`, `P(|uᵀ(V̄_T − V^π)| ≤ z√(uᵀΛ̂_Tu/T)) → 2Φ(z) − 1`;
(D3) for all `z ≥ 0`, `η > 0`, eventually
`P(∀ s, |V̄_T(s) − V^π(s)| ≤ z√(Λ̂_T(s,s)/T)) ≥ 1 − 2S(1 − Φ(z)) − η`. -/
theorem plugin_coverage_tendsto [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    (∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ,
      Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | ∑ s, u s * prAverage M η₀ V₀ ω' s -
            z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') / T) ≤
            ∑ s, u s * M.valueFixedPoint π s}.indicator 1 ω) atTop
        (𝓝 ((gaussianReal 0 1).real (Set.Iic z)))) ∧
    (∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ, 0 ≤ z →
      Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action |
            |∑ s, u s * (prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s)| ≤
              z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') / T)}.indicator
            1 ω) atTop
        (𝓝 (2 * (gaussianReal 0 1).real (Set.Iic z) - 1))) ∧
    (∀ z : ℝ, 0 ≤ z → ∀ η : ℝ, 0 < η →
      ∀ᶠ T : ℕ in atTop,
        1 - 2 * (Fintype.card State : ℝ) * (1 - (gaussianReal 0 1).real (Set.Iic z)) - η ≤
          ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∀ s,
              |prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s| ≤
                z * Real.sqrt (lambdaHat M η₀ V₀ ω' s s / T)}.indicator 1 ω) :=
  ⟨fun _ hu z ↦ tendsto_coverage_oneSided_plugin M π μ h0 h1 V₀ hμ hΓ hu z,
    fun _ hu _ hz ↦ tendsto_coverage_twoSided_plugin M π μ h0 h1 V₀ hμ hΓ hu hz,
    fun _ hz _ hη ↦ eventually_coverage_rect_plugin_ge M π μ h0 h1 V₀ hμ hΓ hz hη⟩

/-! ## Non-vacuity on the one-state instance -/

open OneState in

/-- The hypotheses are satisfiable: on the one-state instance (`oMDP`, `oPolicy`, `oMu`,
`TDInferenceC47Evidence711.lean`; `Γ_true = 1/4 > 0`) with `η₀ = 1/8` and `V₀ = 0`, the
one-sided plug-in coverage in direction `u = 1` tends to `Φ(z)`. -/
theorem oneState_tendsto_coverage_oneSided_plugin (z : ℝ) :
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple Unit (Fin 2), pathWeight oMDP oPolicy oMu ω *
        {ω' : Fin T → Tuple Unit (Fin 2) | ∑ s, (fun _ ↦ (1 : ℝ)) s *
            prAverage oMDP (1 / 8) (fun _ ↦ 0) ω' s -
          z * Real.sqrt ((∑ s, ∑ s', (fun _ ↦ (1 : ℝ)) s * (fun _ ↦ (1 : ℝ)) s' *
            lambdaHat oMDP (1 / 8) (fun _ ↦ 0) ω' s s') / T) ≤
          ∑ s, (fun _ ↦ (1 : ℝ)) s * oMDP.valueFixedPoint oPolicy s}.indicator 1 ω) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Iic z))) :=
  tendsto_coverage_oneSided_plugin oMDP oPolicy oMu (by norm_num) (by norm_num) _
    (fun s ↦ by rw [oMu_prob]; norm_num) (fun s ↦ by rw [oneState_trueGamma]; norm_num)
    (fun h ↦ by simpa using congrFun h ()) z

end StatisticalRL.Ch7Rest.TDInference

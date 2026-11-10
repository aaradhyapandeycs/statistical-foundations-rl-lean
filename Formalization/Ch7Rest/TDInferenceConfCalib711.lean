import Mathlib.Probability.CDF
import Formalization.Ch7Rest.TDInferenceConfRegion711

/-!
# Exact `1 − α` levels for the oracle-covariance confidence regions

Source: `chapters/inference.tex:198–213` (rectangles :198–205, ellipsoids :207–213) and
`docs/SOURCE-ISSUES.md` C47(2)/(3). These are **corrected and oracle-restricted forms, not the
printed formulas**.

Let `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (`trueLambda`, the **oracle** covariance, unknown in practice) and
`N(0,Λ) = gaussCov (tdA M π μ) (trueGamma M π μ)`. Under full-support `μ`, `Γ_true ≻ 0` and
`S ≥ 1` (`Nonempty State`):

* `exists_ellipsoid_level_eq`: for every `α ∈ (0,1)` there is `q ≥ 0` with
  `N(0,Λ){x | xᵀΛ⁻¹x ≤ q} = 1 − α` exactly (corrected ellipsoid, threshold `q`, C47(3));
* `exists_supBox_level_eq`: for every `α ∈ (0,1)` there is `r ≥ 0` with
  `N(0,Λ){x | ∀ s, |x s| ≤ r} = 1 − α` exactly (corrected rectangle, half-width `r/√T`, C47(2));
* `exists_confRegion_oracle_calibrated`: one **instance constant** `K₀ > 0` (it may depend on
  `M, π, μ, η₀, V₀`) such that for every `α ∈ (0,1)` these levels `q_α, r_α` (independent of `T`)
  give, for all `T ≥ 1`,
  `|P(T (V^π − V̄_T)ᵀ Λ⁻¹ (V^π − V̄_T) ≤ q_α) − (1 − α)| ≤ K₀ T^{-1/3} log(2T)` and
  `|P(∀ s, |V̄_T(s) − V^π(s)| ≤ r_α/√T) − (1 − α)| ≤ K₀ T^{-1/3} log(2T)`.
  The rate carries the extra factor `log(2T)` relative to the printed `T^{-1/3}`.

Route: for `g` the quadratic form `xᵀΛ⁻¹x` (resp. the sup norm), the map `q ↦ N{g ≤ q}` is the cdf
of the image law `N ∘ g⁻¹`; its atoms `N{g = q}` vanish because level sets with `q > 0` lie in the
frontier of the convex sublevel set (positive homogeneity), convex frontiers are `N`-null
(`tdGaussCov_frontier_convex_eq_zero`), and `{g ≤ 0} = {0}` is null. The cdf is then continuous,
`0` at `0` and tends to `1`, so the intermediate value theorem gives the exact level.

The identification of `N(0,Λ){xᵀΛ⁻¹x ≤ q}` with the `χ²(S)` cdf is proved downstream in
`Formalization/Ch7Rest/TDInferenceConfChiSq711.lean` (`gaussCov_ellipsoid_eq_chiSquared`), so `q_α` is
the `χ²(S)` `(1 − α)`-quantile (the threshold is `R`, not the printed `R²`, C47(3)). Not proved: the
`ℓ∞` quantile formula for `r_α`, the plug-in covariance `Λ̂_T` with a rate, and the printed rate without
`log(2T)`.
-/

open MeasureTheory ProbabilityTheory Finset Matrix Filter Topology
open StatisticalRL.Probability

namespace StatisticalRL.Ch7Rest.TDInference

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point of `C` whose dilates `t • x`, `t > 1`, all leave `C` lies on the frontier of `C`. -/
theorem confCalib_mem_frontier_of_smul {C : Set E} {x : E} (hx : x ∈ C)
    (h : ∀ t : ℝ, 1 < t → t • x ∉ C) : x ∈ frontier C := by
  refine ⟨subset_closure hx, fun hint ↦ ?_⟩
  have hC : C ∈ 𝓝 x := mem_interior_iff_mem_nhds.1 hint
  have ht : Tendsto (fun t : ℝ ↦ t • x) (𝓝[>] 1) (𝓝 x) := by
    have h1 : Tendsto (fun t : ℝ ↦ t • x) (𝓝 1) (𝓝 ((1 : ℝ) • x)) :=
      (continuous_id.smul continuous_const).tendsto 1
    rw [one_smul] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  obtain ⟨t, h1, h2⟩ := ((ht.eventually_mem hC).and eventually_mem_nhdsWithin).exists
  exact h t h2 h1

end Generic

/-- **Exact levels for an atomless real statistic.** If `ν` is a probability measure, `g` is
measurable, `ν{g = q} = 0` for every `q` and `ν{g ≤ 0} = 0`, then every `p ∈ [0,1)` is attained:
`ν{g ≤ q} = p` for some `q ≥ 0`. -/
theorem confCalib_exists_level_eq {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] {g : Ω → ℝ} (hg : Measurable g)
    (hatom : ∀ q, ν {x | g x = q} = 0) (h0 : ν {x | g x ≤ 0} = 0) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p < 1) : ∃ q : ℝ, 0 ≤ q ∧ ν.real {x | g x ≤ q} = p := by
  set ρ := ν.map g with hρ
  haveI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hF : ∀ q, cdf ρ q = ν.real {x | g x ≤ q} := fun q ↦ by
    rw [cdf_eq_real, hρ, map_measureReal_apply hg measurableSet_Iic]
    rfl
  have hcont : Continuous (cdf ρ) := by
    refine continuous_iff_continuousAt.2 fun a ↦ ?_
    have hsing : (cdf ρ).measure {a} = 0 := by
      rw [measure_cdf, hρ, Measure.map_apply hg (measurableSet_singleton a)]
      exact hatom a
    rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hsing
    rw [(cdf ρ).mono.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
    exact le_antisymm ((cdf ρ).mono.leftLim_le le_rfl) (by linarith)
  have hF0 : cdf ρ 0 = 0 := by rw [hF, measureReal_def, h0, ENNReal.toReal_zero]
  obtain ⟨Q, hpQ, hQ0⟩ :=
    (((tendsto_cdf_atTop ρ).eventually (lt_mem_nhds hp1)).and (eventually_ge_atTop 0)).exists
  obtain ⟨c, hc, hcq⟩ := intermediate_value_Icc hQ0 hcont.continuousOn
    (show p ∈ Set.Icc (cdf ρ 0) (cdf ρ Q) from ⟨by rw [hF0]; exact hp0, hpQ.le⟩)
  exact ⟨c, hc.1, (hF c).symm.trans hcq⟩

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

section TD

variable [Nonempty State] (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
  (μ : FiniteDistribution State)

/-- Convex frontiers are null for `N(0,Λ)` under full-support `μ` and `Γ_true ≻ 0`. -/
theorem confCalib_frontier_null (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s)
    {K : Set (State → ℝ)} (hK : Convex ℝ K) :
    gaussCov (tdA M π μ) (trueGamma M π μ) (frontier K) = 0 :=
  tdGaussCov_frontier_convex_eq_zero M π μ
    (μmin := Finset.univ.inf' Finset.univ_nonempty μ.prob)
    ((Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s) (fun s ↦ Finset.inf'_le _ (mem_univ s)) hΓ hK

/-- `N(0,Λ){0} = 0` (`S ≥ 1`). -/
theorem confCalib_singleton_null (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    gaussCov (tdA M π μ) (trueGamma M π μ) {0} = 0 := by
  rw [measure_eq_interior_of_frontier_null
    (confCalib_frontier_null M π μ hμ hΓ (convex_singleton (0 : State → ℝ))),
    interior_singleton, measure_empty]

/-- Exact `N(0,Λ)` levels for a nonnegative, positively homogeneous-type statistic `g` with convex
sublevel sets and `g = 0` only at `0`. -/
theorem confCalib_exists_level_of_homog (hμ : ∀ s, 0 < μ.prob s)
    (hΓ : ∀ s, 0 < trueGamma M π μ s) {g : (State → ℝ) → ℝ} (hg : Continuous g)
    (hconv : ∀ q, Convex ℝ {x | g x ≤ q}) (hnn : ∀ x, 0 ≤ g x)
    (hzero : ∀ x, g x = 0 → x = 0) (hhom : ∀ x (t : ℝ), 1 < t → 0 < g x → g x < g (t • x))
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ (gaussCov (tdA M π μ) (trueGamma M π μ)).real {x | g x ≤ q} = 1 - α := by
  have hsub0 : ∀ q ≤ (0 : ℝ), {x | g x ≤ q} ⊆ {0} := fun q hq x hx ↦
    hzero x (le_antisymm (le_trans hx hq) (hnn x))
  refine confCalib_exists_level_eq _ hg.measurable (fun q ↦ ?_)
    (measure_mono_null (hsub0 0 le_rfl) (confCalib_singleton_null M π μ hμ hΓ))
    (by linarith) (by linarith)
  rcases le_or_gt q 0 with hq | hq
  · exact measure_mono_null (fun x hx ↦ hsub0 q hq (le_of_eq (Set.mem_setOf_eq ▸ hx)))
      (confCalib_singleton_null M π μ hμ hΓ)
  · refine measure_mono_null (fun x hx ↦ ?_) (confCalib_frontier_null M π μ hμ hΓ (hconv q))
    have hx' : g x = q := hx
    refine confCalib_mem_frontier_of_smul (le_of_eq hx') fun t ht hmem ↦ ?_
    have := hhom x t ht (hx' ▸ hq)
    have hmem' : g (t • x) ≤ q := hmem
    linarith

omit [DecidableEq State] [Nonempty State] in
/-- The quadratic form `xᵀΛ⁻¹x` scales by `t²`. -/
theorem confCalib_quadForm_smul (L : Matrix State State ℝ) (t : ℝ) (x : State → ℝ) :
    ∑ s, ∑ s', (t • x) s * (t • x) s' * L s s' = t ^ 2 * ∑ s, ∑ s', x s * x s' * L s s' := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s' _ ↦ by ring

/-- **Exact `1 − α` level of the corrected ellipsoid (C47(3), oracle `Λ`).** For full-support `μ`,
`Γ_true ≻ 0`, `S ≥ 1` and every `α ∈ (0,1)` there is `q ≥ 0` with
`N(0,Λ){x | xᵀΛ⁻¹x ≤ q} = 1 − α`, `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`. (That `q` is the `χ²(S)` quantile is
proved downstream, `gaussCov_ellipsoid_eq_chiSquared` in `TDInferenceConfChiSq711`.) -/
theorem exists_ellipsoid_level_eq (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ (gaussCov (tdA M π μ) (trueGamma M π μ)).real
      {x | ∑ s, ∑ s', x s * x s' * (trueLambda M π μ)⁻¹ s s' ≤ q} = 1 - α := by
  have hA : IsUnit (tdA M π μ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ
      (μmin := Finset.univ.inf' Finset.univ_nonempty μ.prob)
      ((Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s) (fun s ↦ Finset.inf'_le _ (mem_univ s)))
  refine confCalib_exists_level_of_homog M π μ hμ hΓ (by fun_prop)
    (convex_trueLambda_ellipsoid M π μ hμ hΓ) (fun x ↦ ?_) (fun x hx ↦ ?_)
    (fun x t ht hpos ↦ ?_) hα0 hα1
  · rw [quadForm_trueLambda_inv M π μ hμ hΓ x]
    exact Finset.sum_nonneg fun r _ ↦ mul_nonneg (sq_nonneg _) (inv_pos.2 (hΓ r)).le
  · rw [quadForm_trueLambda_inv M π μ hμ hΓ x] at hx
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun r _ ↦
      mul_nonneg (sq_nonneg _) (inv_pos.2 (hΓ r)).le).1 hx
    have hAx : tdA M π μ *ᵥ x = 0 := by
      funext r
      have h := hterm r (mem_univ r)
      rcases mul_eq_zero.1 h with h | h
      · have h' := pow_eq_zero_iff (two_ne_zero) |>.1 h
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
        rw [← h']
        exact Finset.sum_congr rfl fun s _ ↦ mul_comm _ _
      · exact absurd h (inv_pos.2 (hΓ r)).ne'
    calc x = ((tdA M π μ)⁻¹ * tdA M π μ) *ᵥ x := by
          rw [Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hAx, Matrix.mulVec_zero]
  · rw [confCalib_quadForm_smul]
    exact lt_mul_of_one_lt_left hpos (one_lt_pow₀ ht two_ne_zero)

omit [Fintype State] [DecidableEq State] in
/-- The sup-norm box is the closed sup-norm ball: `{x | ∀ s, |x s| ≤ r} = {x | ‖x‖ ≤ r}`. -/
theorem confCalib_supBox_eq_norm [Fintype State] (r : ℝ) :
    {x : State → ℝ | ∀ s, |x s| ≤ r} = {x | ‖x‖ ≤ r} := by
  ext x
  simp only [Set.mem_setOf_eq]
  by_cases hr : 0 ≤ r
  · rw [pi_norm_le_iff_of_nonneg hr]
    simp only [Real.norm_eq_abs]
  · push_neg at hr
    obtain ⟨s⟩ := (inferInstance : Nonempty State)
    constructor
    · intro h; exact absurd (h s) (not_le.2 (hr.trans_le (abs_nonneg _)))
    · intro h; exact absurd h (not_le.2 (hr.trans_le (norm_nonneg _)))

/-- **Exact `1 − α` level of the corrected rectangle (C47(2), oracle `Λ`).** For full-support `μ`,
`Γ_true ≻ 0`, `S ≥ 1` and every `α ∈ (0,1)` there is `r ≥ 0` with
`N(0,Λ){x | ∀ s, |x s| ≤ r} = 1 − α`. -/
theorem exists_supBox_level_eq (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ (gaussCov (tdA M π μ) (trueGamma M π μ)).real
      {x | ∀ s, |x s| ≤ r} = 1 - α := by
  simp_rw [confCalib_supBox_eq_norm]
  refine confCalib_exists_level_of_homog M π μ hμ hΓ continuous_norm (fun q ↦ ?_) norm_nonneg
    (fun x hx ↦ norm_eq_zero.1 hx) (fun x t ht hpos ↦ ?_) hα0 hα1
  · rw [← confCalib_supBox_eq_norm]
    exact convex_supBox q
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans ht)]
    exact lt_mul_of_one_lt_left hpos ht

/-- **Calibrated oracle-covariance confidence regions (corrected C47(2)/(3), extra `log(2T)`).**
For full-support `μ`, `0 < η₀ ≤ 1`, every `V₀`, `Γ_true ≻ 0` and `S ≥ 1`, with
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (oracle covariance, unknown in practice), there is one instance
constant `K₀ > 0` such that for every `α ∈ (0,1)` there are levels `q_α ≥ 0`, `r_α ≥ 0`
(independent of `T`) with `N(0,Λ){xᵀΛ⁻¹x ≤ q_α} = 1 − α`, `N(0,Λ){‖x‖∞ ≤ r_α} = 1 − α`, and for
all `T ≥ 1`:
`|P(T (V^π − V̄_T)ᵀ Λ⁻¹ (V^π − V̄_T) ≤ q_α) − (1 − α)| ≤ K₀ T^{-1/3} log(2T)` and
`|P(∀ s, V̄_T(s) − r_α/√T ≤ V^π(s) ≤ V̄_T(s) + r_α/√T) − (1 − α)| ≤ K₀ T^{-1/3} log(2T)`.
Not the printed formulas (threshold `q` instead of `R²`, `√T` applied once, oracle `Λ`); the
`χ²(S)` identification of `q_α` is proved downstream (`exists_confRegion_oracle_chiSquared` in
`TDInferenceConfChiSq711`); the `ℓ∞` quantile formula for `r_α` is not proved. -/
theorem exists_confRegion_oracle_calibrated (hμ : ∀ s, 0 < μ.prob s) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
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
            K₀ * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)) ∧
          |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
              {ω' : Fin T → Tuple State Action | ∀ s,
                prAverage M η₀ V₀ ω' s - r / Real.sqrt T ≤ M.valueFixedPoint π s ∧
                  M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + r / Real.sqrt T}.indicator 1 ω -
              (1 - α)| ≤
            K₀ * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)) := by
  obtain ⟨K₀, hK₀, hb⟩ := exists_confRegion_oracle_bounds M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K₀, hK₀, fun α hα0 hα1 ↦ ?_⟩
  obtain ⟨q, hq0, hq⟩ := exists_ellipsoid_level_eq M π μ hμ hΓ hα0 hα1
  obtain ⟨r, hr0, hr⟩ := exists_supBox_level_eq M π μ hμ hΓ hα0 hα1
  refine ⟨q, hq0, r, hr0, hq, hr, fun T hT ↦ ⟨?_, ?_⟩⟩
  · rw [← hq]; exact (hb T hT).2.1 q
  · rw [← hr]; exact (hb T hT).2.2 r

end TD

end StatisticalRL.Ch7Rest.TDInference

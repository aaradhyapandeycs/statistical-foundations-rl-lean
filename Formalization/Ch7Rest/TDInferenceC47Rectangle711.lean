import Formalization.Ch7Rest.TDInferencePluginCoverage711
import Formalization.Probability.GaussianQuantile

/-!
# C47(2) evidence: the printed hyper-rectangle under-covers (coverage → 0)

Source: `chapters/inference.tex:198–205` (item (i), "Hyper-rectangles"): the set
`C_α = ∏_s [V̄_T(s) − R̂/√T, V̄_T(s) + R̂/√T]` (display :201–203), where `R̂ > 0` is "the (random)
quantile of the `ℓ∞` norm of a centered Gaussian random vector with covariance `Λ̂_T/T`" (:205);
the rule `eq:convex.Cdelta` (:187–196); SOURCE-ISSUES C47(2).

**The issue.** `R̂` is already a quantile of `‖N(0, Λ̂_T/T)‖∞`, so `R̂ = O(T^{-1/2})`, and the
printed half-width `R̂/√T` applies the `√T` scaling a second time: it is `O(1/T)`, while the
estimation error `V̄_T − V^π` is of order `T^{-1/2}`. Hence the coverage tends to `0`.

**Instance.** The one-state instance O of `TDInferenceC47Evidence711.lean` (`State = Unit`,
`S = 1`, rewards `0, 1`, `γ = 1/2`, uniform `π` and `μ`): `V^π = 1`, `Γ_true = 1/4`, oracle
covariance `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ = 1`. Every `0 < η₀ ≤ 1` (containing the printed range)
and every initialisation `V₀` are allowed.

**Encoding of the quantile.** With `S = 1`, a centered Gaussian vector `X : Unit → ℝ` with
covariance `c` has `‖X‖∞ = |X ()|`, and `X ()` has law `N(0, c)` (`gaussianReal 0 c`). The
level is `1 − α` (implicit in the source, from `eq:convex.Cdelta`). `R` is required to be the
lower `(1 − α)`-quantile: `P(|X| ≤ R) ≥ 1 − α` and `P(|X| ≤ R') < 1 − α` for every `R' < R`
(only the second half is used by the proofs). The variance is `(c).toNNReal`, which equals `c`
whenever `c ≥ 0` (always the case for `Λ/T`; for `Λ̂_T/T` see below).

* `C47_rectangle_printed_undercovers` (**oracle covariance** `Λ` in place of `Λ̂_T`): the coverage
  `P(V^π ∈ C_α)` tends to `0`. Proved by `c47_rectangle_printed_undercovers` from the
  quantitative bound `oracleRectangle_coverage_le`:
  `P(V^π ∈ C_α) ≤ 2Φ(z/√T) − 1 + 2K T^{-1/3}` with `2Φ(z) − 1 ≥ 1 − α`, a corollary of the
  half-space Theorem 7.11 result (`abs_coverage_twoSided_sub_le`, no CLT).
* `C47_rectangle_printed_undercovers_plugin` (the **printed plug-in** `Λ̂_T = lambdaHat`,
  quantile taken pathwise): the coverage again tends to `0`. Proved by
  `c47_rectangle_printed_undercovers_plugin` from the plug-in two-sided limit
  `tendsto_coverage_twoSided_plugin` (which rests on the consistency
  `eq_defn_hat_Lambda_corrected`); qualitative only (no rate).
* Non-vacuity: the quantile hypotheses are satisfiable, with the exact quantile
  `R = z√(c)`, `2Φ(z) − 1 = 1 − α` (`exists_oracle_rectangle_quantile`,
  `exists_plugin_rectangle_quantile`).

The general standard-Gaussian quantile lemmas (`le_mul_sqrt_of_quantile`, `isQuantile_mul_sqrt`,
...) live in `Formalization/Probability/GaussianQuantile.lean`.

Scope: one instance (`S = 1`) suffices to refute the printed universal claim that the rectangle is
an (approximate) `1 − α` confidence region. For `S = 1` the `ℓ∞` quantile is the two-sided
Gaussian quantile; nothing about the multi-dimensional `ℓ∞` quantile is formalized here. On paths
where `Λ̂_T(·,·) < 0` (none in instance O, where `Λ̂_T = 4Γ̂_T ≥ 0`, but not used) the Gaussian
`N(0, Λ̂_T/T)` is read as `N(0, 0)` via `toNNReal`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open scoped BigOperators NNReal

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Probability.Stein

private theorem sqrt_coe_toNNReal (x : ℝ) : Real.sqrt (x.toNNReal : ℝ) = Real.sqrt x := by
  rcases le_total 0 x with hx | hx
  · rw [Real.coe_toNNReal _ hx]
  · rw [Real.toNNReal_of_nonpos hx, NNReal.coe_zero, Real.sqrt_zero,
      Real.sqrt_eq_zero_of_nonpos hx]

/-! ## Local helpers -/

section PathSum

variable {State Action : Type} [Fintype State] [Fintype Action]

private theorem sum_pathWeight_indicator_nonneg (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ}
    (s : Set (Fin T → Tuple State Action)) :
    0 ≤ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * s.indicator 1 ω :=
  Finset.sum_nonneg fun ω _ ↦ mul_nonneg (pathWeight_nonneg M π μ ω)
    (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) ω)

private theorem sum_pathWeight_indicator_mono (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ}
    {s t : Set (Fin T → Tuple State Action)} (h : s ⊆ t) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * s.indicator 1 ω ≤
      ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * t.indicator 1 ω :=
  Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left
    (Set.indicator_le_indicator_of_subset h (fun _ ↦ zero_le_one) ω) (pathWeight_nonneg M π μ ω)

end PathSum

/-- Membership in the rectangle `∏_s [V̄(s) − h, V̄(s) + h]` (here `S = 1`) gives `|V̄ − V| ≤ h`. -/
private theorem abs_sub_le_of_mem_pi_Icc {V Vbar : Unit → ℝ} {h : ℝ}
    (hm : V ∈ Set.univ.pi fun s ↦ Set.Icc (Vbar s - h) (Vbar s + h)) : |Vbar () - V ()| ≤ h := by
  have h1 := (Set.mem_univ_pi.1 hm) ()
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

private theorem sqrt_one_div_eq (T : ℝ) : Real.sqrt (1 / T) = 1 / Real.sqrt T := by
  rw [one_div, Real.sqrt_inv, one_div]

private theorem tendsto_mul_sqrt_one_div (z : ℝ) :
    Tendsto (fun T : ℕ ↦ z * Real.sqrt (1 / (T : ℝ))) atTop (𝓝 0) := by
  have h := ((Real.continuous_sqrt.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat).const_mul z
  simpa [Real.sqrt_zero] using h

open OneState

/-! ## The printed rectangle, oracle covariance -/

/-- **C47(2), printed rectangle, oracle covariance (library Prop, not a statement-index entry).**
On instance O (`S = 1`, oracle `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`, which equals `1` here), for every
`0 < η₀ ≤ 1`, `V₀`, `0 < α < 1` and every sequence `R_T` that is the `(1 − α)`-quantile of the
`ℓ∞` norm `|X|` of `X ∼ N(0, Λ/T)` (`inference.tex:205`, oracle `Λ` in place of `Λ̂_T`), the
coverage of the printed rectangle `∏_s [V̄_T(s) − R_T/√T, V̄_T(s) + R_T/√T]` (:201–203) tends
to `0`. SOURCE-ISSUES C47(2). -/
def C47_rectangle_printed_undercovers : Prop :=
  ∀ η₀ : ℝ, 0 < η₀ → η₀ ≤ 1 → ∀ V₀ : Unit → ℝ, ∀ α : ℝ, 0 < α → α < 1 →
  ∀ R : ℕ → ℝ, (∀ T : ℕ, 1 ≤ T →
      1 - α ≤ (gaussianReal 0 (Real.toNNReal (((tdA oMDP oPolicy oMu)⁻¹ *
          diagonal (trueGamma oMDP oPolicy oMu) * (tdA oMDP oPolicy oMu)⁻¹ᵀ) () () / T))).real
        {x | |x| ≤ R T} ∧
      ∀ R' : ℝ, R' < R T →
        (gaussianReal 0 (Real.toNNReal (((tdA oMDP oPolicy oMu)⁻¹ *
          diagonal (trueGamma oMDP oPolicy oMu) * (tdA oMDP oPolicy oMu)⁻¹ᵀ) () () / T))).real
          {x | |x| ≤ R'} < 1 - α) →
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple Unit (Fin 2), pathWeight oMDP oPolicy oMu ω *
        {ω' : Fin T → Tuple Unit (Fin 2) | oMDP.valueFixedPoint oPolicy ∈
          Set.univ.pi fun s ↦ Set.Icc (prAverage oMDP η₀ V₀ ω' s - R T / Real.sqrt T)
            (prAverage oMDP η₀ V₀ ω' s + R T / Real.sqrt T)}.indicator 1 ω) atTop (𝓝 0)

/-- Two-sided oracle interval on instance O at level `ℓ`, in scalar form. -/
theorem oneState_twoSided_oracle {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : Unit → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ ℓ : ℝ, 0 ≤ ℓ →
      (∑ ω : Fin T → Tuple Unit (Fin 2), pathWeight oMDP oPolicy oMu ω *
          {ω' : Fin T → Tuple Unit (Fin 2) |
            |prAverage oMDP η₀ V₀ ω' () - oMDP.valueFixedPoint oPolicy ()| ≤
              ℓ * Real.sqrt (1 / T)}.indicator 1 ω) ≤
        2 * stdCDF ℓ - 1 + 2 * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hμ : ∀ s, 0 < oMu.prob s := fun s ↦ by rw [oMu_prob]; norm_num
  have hΓ : ∀ s, 0 < trueGamma oMDP oPolicy oMu s := fun s ↦ by
    rw [oneState_trueGamma]; norm_num
  obtain ⟨K, hK, hb⟩ := abs_coverage_twoSided_sub_le oMDP oPolicy oMu h0 h1 V₀ hμ hΓ
  refine ⟨K, hK, fun T hT ℓ hℓ ↦ ?_⟩
  have h := hb T hT (fun _ ↦ 1) (fun h ↦ by simpa using congrFun h ()) ℓ hℓ
  simp only [oneState_oracleLambda, Fintype.univ_unit, Finset.sum_singleton, one_mul,
    mul_one, gaussianReal_real_Iic] at h
  linarith [(abs_le.1 h).2]

/-- **Quantitative form.** With `z ≥ 0`, `2Φ(z) − 1 ≥ 1 − α` (`α < 1`), the printed rectangle
with any `R_T` below the oracle quantile has coverage `≤ 2Φ(z/√T) − 1 + 2K T^{-1/3}`. -/
theorem oracleRectangle_coverage_le {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : Unit → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ α z : ℝ, 0 ≤ z → 1 - α ≤ 2 * stdCDF z - 1 → ∀ T : ℕ, 1 ≤ T →
      ∀ R : ℝ, (∀ R' : ℝ, R' < R →
        (gaussianReal 0 (Real.toNNReal (((tdA oMDP oPolicy oMu)⁻¹ *
          diagonal (trueGamma oMDP oPolicy oMu) * (tdA oMDP oPolicy oMu)⁻¹ᵀ) () () / T))).real
          {x | |x| ≤ R'} < 1 - α) →
      (∑ ω : Fin T → Tuple Unit (Fin 2), pathWeight oMDP oPolicy oMu ω *
        {ω' : Fin T → Tuple Unit (Fin 2) | oMDP.valueFixedPoint oPolicy ∈
          Set.univ.pi fun s ↦ Set.Icc (prAverage oMDP η₀ V₀ ω' s - R / Real.sqrt T)
            (prAverage oMDP η₀ V₀ ω' s + R / Real.sqrt T)}.indicator 1 ω) ≤
        2 * stdCDF (z * Real.sqrt (1 / T)) - 1 + 2 * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := oneState_twoSided_oracle h0 h1 V₀
  refine ⟨K, hK, fun α z hz hzα T hT R hR ↦ ?_⟩
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  simp only [oneState_oracleLambda] at hR
  have hRle := le_mul_sqrt_of_quantile _ hz hzα hR
  rw [Real.coe_toNNReal _ (by positivity)] at hRle
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT'
  refine le_trans (sum_pathWeight_indicator_mono _ _ _ fun ω' hω' ↦ ?_)
    (hb T hT _ (mul_nonneg hz (Real.sqrt_nonneg _)))
  have habs := abs_sub_le_of_mem_pi_Icc hω'
  simp only [Set.mem_setOf_eq]
  refine habs.trans ?_
  rw [div_le_iff₀ hsT]
  calc R ≤ z * Real.sqrt (1 / T) := hRle
    _ = z * Real.sqrt (1 / T) * Real.sqrt (1 / T) * Real.sqrt T := by
        rw [sqrt_one_div_eq]; field_simp

/-- **C47(2), oracle covariance: the printed rectangle's coverage tends to `0`.** -/
theorem c47_rectangle_printed_undercovers : C47_rectangle_printed_undercovers := by
  intro η₀ h0 h1 V₀ α hα0 _ R hR
  obtain ⟨z, hz, hzα⟩ := exists_two_mul_stdCDF_sub_one_ge hα0
  obtain ⟨K, _, hb⟩ := oracleRectangle_coverage_le h0 h1 V₀
  have hlim : Tendsto (fun T : ℕ ↦ (T : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hΦ := (continuous_stdCDF.tendsto 0).comp (tendsto_mul_sqrt_one_div z)
  have hup : Tendsto (fun T : ℕ ↦ 2 * stdCDF (z * Real.sqrt (1 / (T : ℝ))) - 1 +
      2 * K * (T : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    have h := ((hΦ.const_mul 2).sub_const 1).add (hlim.const_mul (2 * K))
    rw [stdCDF_zero] at h
    convert h using 2
    norm_num
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun T ↦ sum_pathWeight_indicator_nonneg _ _ _ _) ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  exact hb α z hz hzα T hT (R T) (hR T hT).2

/-- Non-vacuity of `C47_rectangle_printed_undercovers`: the exact oracle quantile
`R_T = z√(Λ/T)` (`2Φ(z) − 1 = 1 − α`) satisfies the quantile hypotheses. -/
theorem exists_oracle_rectangle_quantile {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ R : ℕ → ℝ, ∀ T : ℕ, 1 ≤ T →
      1 - α ≤ (gaussianReal 0 (Real.toNNReal (((tdA oMDP oPolicy oMu)⁻¹ *
          diagonal (trueGamma oMDP oPolicy oMu) * (tdA oMDP oPolicy oMu)⁻¹ᵀ) () () / T))).real
        {x | |x| ≤ R T} ∧
      ∀ R' : ℝ, R' < R T →
        (gaussianReal 0 (Real.toNNReal (((tdA oMDP oPolicy oMu)⁻¹ *
          diagonal (trueGamma oMDP oPolicy oMu) * (tdA oMDP oPolicy oMu)⁻¹ᵀ) () () / T))).real
          {x | |x| ≤ R'} < 1 - α := by
  obtain ⟨z, hz, hzα⟩ := exists_two_mul_stdCDF_sub_one_eq hα0 hα1
  exact ⟨fun T ↦ z * Real.sqrt (Real.toNNReal (((tdA oMDP oPolicy oMu)⁻¹ *
      diagonal (trueGamma oMDP oPolicy oMu) * (tdA oMDP oPolicy oMu)⁻¹ᵀ) () () / T) : ℝ),
    fun T _ ↦ isQuantile_mul_sqrt _ hz hzα hα1⟩

/-! ## The printed rectangle, plug-in covariance -/

/-- **C47(2), printed rectangle, printed plug-in covariance (library Prop).** As
`C47_rectangle_printed_undercovers`, but with the printed plug-in `Λ̂_T = lambdaHat`
(`eq:defn-hat-Lambda`, :180–182): `R_T(ω)` is, pathwise, the `(1 − α)`-quantile of `|X|`,
`X ∼ N(0, Λ̂_T(ω)/T)` (:205). The coverage of the printed rectangle tends to `0`. -/
def C47_rectangle_printed_undercovers_plugin : Prop :=
  ∀ η₀ : ℝ, 0 < η₀ → η₀ ≤ 1 → ∀ V₀ : Unit → ℝ, ∀ α : ℝ, 0 < α → α < 1 →
  ∀ R : (T : ℕ) → (Fin T → Tuple Unit (Fin 2)) → ℝ,
    (∀ T : ℕ, 1 ≤ T → ∀ ω : Fin T → Tuple Unit (Fin 2),
      1 - α ≤ (gaussianReal 0 (Real.toNNReal (lambdaHat oMDP η₀ V₀ ω () () / T))).real
        {x | |x| ≤ R T ω} ∧
      ∀ R' : ℝ, R' < R T ω →
        (gaussianReal 0 (Real.toNNReal (lambdaHat oMDP η₀ V₀ ω () () / T))).real
          {x | |x| ≤ R'} < 1 - α) →
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple Unit (Fin 2), pathWeight oMDP oPolicy oMu ω *
        {ω' : Fin T → Tuple Unit (Fin 2) | oMDP.valueFixedPoint oPolicy ∈
          Set.univ.pi fun s ↦ Set.Icc (prAverage oMDP η₀ V₀ ω' s - R T ω' / Real.sqrt T)
            (prAverage oMDP η₀ V₀ ω' s + R T ω' / Real.sqrt T)}.indicator 1 ω) atTop (𝓝 0)

/-- The plug-in two-sided interval on instance O, scalar form. -/
theorem oneState_tendsto_twoSided_plugin {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : Unit → ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple Unit (Fin 2), pathWeight oMDP oPolicy oMu ω *
        {ω' : Fin T → Tuple Unit (Fin 2) |
          |prAverage oMDP η₀ V₀ ω' () - oMDP.valueFixedPoint oPolicy ()| ≤
            c * Real.sqrt (lambdaHat oMDP η₀ V₀ ω' () () / T)}.indicator 1 ω) atTop
      (𝓝 (2 * stdCDF c - 1)) := by
  have h := tendsto_coverage_twoSided_plugin oMDP oPolicy oMu h0 h1 V₀
    (fun s ↦ by rw [oMu_prob]; norm_num) (fun s ↦ by rw [oneState_trueGamma]; norm_num)
    (u := fun _ ↦ 1) (fun h ↦ by simpa using congrFun h ()) hc
  simpa only [Fintype.univ_unit, Finset.sum_singleton, one_mul, gaussianReal_real_Iic] using h

/-- **C47(2), plug-in covariance: the printed rectangle's coverage tends to `0`.** -/
theorem c47_rectangle_printed_undercovers_plugin : C47_rectangle_printed_undercovers_plugin := by
  intro η₀ h0 h1 V₀ α hα0 _ R hR
  obtain ⟨z, hz, hzα⟩ := exists_two_mul_stdCDF_sub_one_ge hα0
  refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun T ↦
    lt_of_lt_of_le ha (sum_pathWeight_indicator_nonneg _ _ _ _), fun b hb ↦ ?_⟩
  -- choose `c > 0` with `2Φ(c) − 1 < b`
  have hΦ0 : Tendsto stdCDF (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2)) := by
    rw [← stdCDF_zero]; exact (continuous_stdCDF.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨c, hcΦ, hc0⟩ :=
    ((hΦ0.eventually (gt_mem_nhds (by linarith : (1 / 2 : ℝ) < 1 / 2 + b / 2))).and
      self_mem_nhdsWithin).exists
  have hc0' : 0 < c := hc0
  have hcb : 2 * stdCDF c - 1 < b := by linarith
  filter_upwards [(oneState_tendsto_twoSided_plugin h0 h1 V₀ hc0'.le).eventually
      (gt_mem_nhds hcb), (tendsto_mul_sqrt_one_div z).eventually (gt_mem_nhds hc0'),
      eventually_ge_atTop 1] with T hTb hTc hT
  refine lt_of_le_of_lt (sum_pathWeight_indicator_mono _ _ _ fun ω' hω' ↦ ?_) hTb
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT'
  have hRle := le_mul_sqrt_of_quantile _ hz hzα (hR T hT ω').2
  rw [sqrt_coe_toNNReal] at hRle
  have habs := abs_sub_le_of_mem_pi_Icc hω'
  simp only [Set.mem_setOf_eq]
  refine habs.trans ?_
  set L := Real.sqrt (lambdaHat oMDP η₀ V₀ ω' () () / T)
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  calc R T ω' / Real.sqrt T ≤ z * L / Real.sqrt T := div_le_div_of_nonneg_right hRle hsT.le
    _ = z * Real.sqrt (1 / T) * L := by rw [sqrt_one_div_eq]; ring
    _ ≤ c * L := mul_le_mul_of_nonneg_right hTc.le hL

/-- Non-vacuity of `C47_rectangle_printed_undercovers_plugin`: the exact pathwise quantile
`R_T(ω) = z√(Λ̂_T(ω)/T)` (`2Φ(z) − 1 = 1 − α`) satisfies the quantile hypotheses, for every
`η₀`, `V₀` (including paths with `Λ̂_T(ω) = 0`, where `N(0, 0)` is the point mass). -/
theorem exists_plugin_rectangle_quantile (η₀ : ℝ) (V₀ : Unit → ℝ) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ R : (T : ℕ) → (Fin T → Tuple Unit (Fin 2)) → ℝ,
      ∀ T : ℕ, 1 ≤ T → ∀ ω : Fin T → Tuple Unit (Fin 2),
        1 - α ≤ (gaussianReal 0 (Real.toNNReal (lambdaHat oMDP η₀ V₀ ω () () / T))).real
          {x | |x| ≤ R T ω} ∧
        ∀ R' : ℝ, R' < R T ω →
          (gaussianReal 0 (Real.toNNReal (lambdaHat oMDP η₀ V₀ ω () () / T))).real
            {x | |x| ≤ R'} < 1 - α := by
  obtain ⟨z, hz, hzα⟩ := exists_two_mul_stdCDF_sub_one_eq hα0 hα1
  exact ⟨fun T ω ↦ z * Real.sqrt (Real.toNNReal (lambdaHat oMDP η₀ V₀ ω () () / T) : ℝ),
    fun T _ ω ↦ isQuantile_mul_sqrt _ hz hzα hα1⟩

end StatisticalRL.Ch7Rest.TDInference

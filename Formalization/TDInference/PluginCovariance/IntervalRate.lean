import Formalization.TDInference.PluginCovariance.Rate
import Formalization.TDInference.PluginCovariance.Coverage

/-!
# Finite-`T` rate for the plug-in intervals and the Bonferroni box (C47(1) correction)

Source: `chapters/inference.tex:187–196` (the plug-in rule `eq:convex.Cdelta` :189–195: a convex
set with mass `≥ 1 − α` under `N(V̄_T, Λ̂_T/T)`, and the claim :196 that "such sets serve as
approximate confidence regions"), the plug-in covariance `eq:defn-hat-Lambda` :180–182, and
SOURCE-ISSUES C43 (target covariance) and C47 (fixed shapes).

With `Λ̂_T = lambdaHat`, the corrected target `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ = trueLambda` (C43),
`q̂_T(u) = uᵀΛ̂_Tu` and `Φ(z) = N(0,1)(-∞, z]`, write `r_T = T^{-1/3}`:

* one-sided (`exists_abs_coverage_oneSided_plugin_sub_le`): for `u ≠ 0`, `z ∈ ℝ`,
  `|P(uᵀV̄_T − z√(q̂_T(u)/T) ≤ uᵀV^π) − Φ(z)| ≤ K r_T`;
* two-sided (`exists_abs_coverage_twoSided_plugin_sub_le`): for `u ≠ 0`, `z ≥ 0`,
  `|P(|uᵀ(V̄_T − V^π)| ≤ z√(q̂_T(u)/T)) − (2Φ(z) − 1)| ≤ K r_T`;
* Bonferroni box (`exists_coverage_rect_plugin_ge_sub`): for `z ≥ 0`,
  `P(∀ s, |V̄_T(s) − V^π(s)| ≤ z√(Λ̂_T(s,s)/T)) ≥ 1 − 2S(1 − Φ(z)) − K r_T`;
* all three with one constant: `plugin_coverage_rate`.

**Fixed shapes (C47(1)).** The printed rule allows any (possibly data-selected) convex set; that
claim is not what is proved. Here the direction `u` and the level `z` are fixed before the data,
and the box has fixed per-coordinate level `z`.

**Instance constant.** In every statement `∃ K` precedes `∀ T u z`: `K > 0` depends only on the
instance `(M, π, μ, η₀, V₀)` (through the oracle half-space constant of
`exists_abs_lawProb_halfSpace_pivot_sub_le`, the plug-in consistency constant of
`exists_pathProb_lambdaHat_sub_gt_le`, and the ellipticity constant `g/(S R² + 1)` of `Λ` with
`g = min_s Γ_true(s)`, `R = ∑ |A_{rs}|`). It does not depend on `T`, on `u` or on `z`.
The combined export takes the sum of the three constants.

Hypotheses: full-support `μ`, `0 < η₀ ≤ 1` (containing the printed `(0, 1/4)`), every `V₀`,
`Γ_true ≻ 0` (an added non-degeneracy hypothesis, as in the asymptotic
`TDInference/PluginCovariance/Coverage.lean`).

**Route.** Take `ε = r_T` in the plug-in consistency bound `P(∃ s s', ε < |Λ̂_T − Λ|) ≤ C/(ε²T) =
C r_T`. Off that bad event `|q̂ − q| ≤ (∑|u|)² ε ≤ κ q` with `κ = ε / c_ell` (ellipticity
`c_ell (∑|u|)² ≤ q`, uniform in `u`), so `(1 − κ)√q ≤ √q̂ ≤ (1 + κ)√q` and the coverage event is
sandwiched between the deterministic half-spaces at levels `min/max(z(1 ∓ κ))·√q`. The oracle
half-space rate `K₀ r_T` holds at both, and `|Φ(z(1 ± κ)) − Φ(z)| ≤ κ` uniformly in `z` (for
`κ ≤ 1/2`; `abs_stdCDF_div_sub_le_of_le`). If `κ > 1/2` the bound is trivial.

**Junk value (C47(4)).** On the event that some state is unsampled, Lean's `Matrix.inv` gives
`Λ̂_T = 0`; that event lies inside the charged bad event, so the bound does not depend on the
convention.
-/

open MeasureTheory ProbabilityTheory Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Probability.Stein StatisticalRL.Analysis

/-! ## Real-number helpers -/

/-- `|Φ(z(1 + κ)) − Φ(z)| ≤ κ` for `κ ≥ 0`, uniformly in `z`. -/
theorem abs_stdCDF_mul_one_add_sub_le (z : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    |stdCDF (z * (1 + κ)) - stdCDF z| ≤ κ := by
  have ha : (0 : ℝ) < 1 / (1 + κ) := by positivity
  have hab : 1 / (1 + κ) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have h := abs_stdCDF_div_sub_le_of_le z ha hab
  rw [div_one, div_div_eq_mul_div, div_one, abs_sub_comm] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith

/-- `|Φ(z(1 − κ)) − Φ(z)| ≤ κ` for `0 ≤ κ ≤ 1/2`, uniformly in `z`. -/
theorem abs_stdCDF_mul_one_sub_sub_le (z : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (hκ2 : κ ≤ 1 / 2) :
    |stdCDF (z * (1 - κ)) - stdCDF z| ≤ κ := by
  have h1 : (0 : ℝ) < 1 - κ := by linarith
  have hab : (1 : ℝ) ≤ 1 / (1 - κ) := by rw [le_div_iff₀ h1]; linarith
  have h := abs_stdCDF_div_sub_le_of_le z one_pos hab
  rw [div_one, div_div_eq_mul_div, div_one] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by norm_num), div_sub_one h1.ne', div_le_iff₀ h1]
  nlinarith

/-- `min(z l, z h) ≤ z a ≤ max(z l, z h)` for `l ≤ a ≤ h`. -/
theorem mul_mem_min_max {z l a h : ℝ} (hl : l ≤ a) (hh : a ≤ h) :
    min (z * l) (z * h) ≤ z * a ∧ z * a ≤ max (z * l) (z * h) := by
  rcases le_total 0 z with hz | hz
  · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_left hl hz),
      le_max_of_le_right (mul_le_mul_of_nonneg_left hh hz)⟩
  · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_left hh hz),
      le_max_of_le_left (mul_le_mul_of_nonpos_left hl hz)⟩

/-- `r_T = T^{-1/3}` satisfies `r_T³ T = 1` for `T > 0`. -/
theorem rpow_neg_third_pow_three_mul {T : ℝ} (hT : 0 < T) :
    (T ^ (-(1 / 3 : ℝ))) ^ 3 * T = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
  norm_num
  rw [Real.rpow_neg_one, inv_mul_cancel₀ hT.ne']

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

omit [DecidableEq State] in
/-- `P(E) ≤ 1`. -/
theorem pathProb_le_one' (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (T : ℕ) (E : Set (Fin T → Tuple State Action)) :
    pathProb M π μ T E ≤ 1 := by
  have h := pathProb_nonneg M π μ T Eᶜ
  rw [pathProb_compl] at h
  linarith

/-! ## Core: one-sided half-line with the plug-in threshold, at rate `T^{-1/3}` -/

/-- **Core rate.** One instance constant `K > 0` (independent of `T`, `u`, `z`) such that for all
`T ≥ 1`, `u ≠ 0` and `z ∈ ℝ`, `|P(uᵀ√TΔ̄_T ≤ z√(uᵀΛ̂_Tu)) − Φ(z)| ≤ K T^{-1/3}`. -/
theorem exists_abs_pathProb_le_mul_sqrt_quadForm_lambdaHat_sub_le [Nonempty State]
    [Nonempty Action] (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ,
      |pathProb M π μ T {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤
          z * Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s')} -
        (gaussianReal 0 1).real (Set.Iic z)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K₀, hK₀, hb⟩ := exists_abs_lawProb_halfSpace_pivot_sub_le M π μ h0 h1 V₀ hμ hΓ
  obtain ⟨C, hC, hcons⟩ := exists_pathProb_lambdaHat_sub_gt_le M π μ hμ h0 h1 V₀
  -- ellipticity of `Λ` in the `(∑ |u|)²` form
  have hμmin0 : 0 < diagMin μ.prob := (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s
  have hμmin : ∀ s, diagMin μ.prob ≤ μ.prob s := fun s ↦ Finset.inf'_le _ (Finset.mem_univ s)
  have hAu : IsUnit (tdA M π μ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)
  have hg0 : 0 < diagMin (trueGamma M π μ) := (Finset.lt_inf'_iff _).2 fun s _ ↦ hΓ s
  have hg : ∀ s, diagMin (trueGamma M π μ) ≤ trueGamma M π μ s :=
    fun s ↦ Finset.inf'_le _ (Finset.mem_univ s)
  obtain ⟨D, hD⟩ : ∃ D : ℝ,
      D = (Fintype.card State : ℝ) * (∑ r, ∑ s, |tdA M π μ r s|) ^ 2 + 1 := ⟨_, rfl⟩
  have hDpos : 0 < D := hD ▸ by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = diagMin (trueGamma M π μ) / D := ⟨_, rfl⟩
  have hcpos : 0 < c := hc ▸ div_pos hg0 hDpos
  have hell : ∀ u : State → ℝ, c * (∑ s, |u s|) ^ 2 ≤
      ∑ s, ∑ s', u s * u s' * trueLambda M π μ s s' := by
    intro u
    have h := mul_sq_sum_abs_le_quadForm (tdA M π μ) hAu (trueGamma M π μ) hg0.le hg u
    rw [← quadForm_mul_diagonal_mul_transpose, ← hD] at h
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ hDpos, mul_comm _ D]
    exact h
  refine ⟨K₀ + C + 2 / c, by positivity, fun T hT u hu z ↦ ?_⟩
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  set r : ℝ := (T : ℝ) ^ (-(1 / 3 : ℝ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hT0 _
  have hr1 : r ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT) (by norm_num)
  have hr3 : r ^ 3 * T = 1 := rpow_neg_third_pow_three_mul hT0
  rw [gaussianReal_real_Iic]
  set κ : ℝ := r / c with hκ
  have hκ0 : 0 < κ := div_pos hr0 hcpos
  set E : Set (Fin T → Tuple State Action) := {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤
    z * Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s')} with hE
  -- trivial regime
  by_cases hbig : 1 / 2 < κ
  · have hP0 := pathProb_nonneg M π μ T E
    have hP1 := pathProb_le_one' M π μ T E
    have hΦ0 := stdCDF_nonneg z
    have hΦ1 := stdCDF_le_one z
    have h2 : 1 ≤ 2 / c * r := by
      rw [hκ] at hbig
      rw [div_mul_eq_mul_div, le_div_iff₀ hcpos]
      rw [lt_div_iff₀ hcpos] at hbig
      linarith
    have : |pathProb M π μ T E - stdCDF z| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hK0r : 0 ≤ (K₀ + C) * r := by positivity
    calc _ ≤ 1 := this
      _ ≤ (K₀ + C) * r + 2 / c * r := by linarith
      _ = (K₀ + C + 2 / c) * r := by ring
  push_neg at hbig
  -- the bad event and its probability
  set B : Set (Fin T → Tuple State Action) :=
    {ω | ∃ s s', r < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|} with hB
  have hPB : pathProb M π μ T B ≤ C * r := by
    refine (hcons T hT r hr0 hr1).trans (le_of_eq ?_)
    rw [div_eq_iff (by positivity)]
    calc C = C * (r ^ 3 * T) := by rw [hr3, mul_one]
      _ = C * r * (r ^ 2 * T) := by ring
  set q : ℝ := ∑ s, ∑ s', u s * u s' * trueLambda M π μ s s' with hq
  have hqpos : 0 < q := quadForm_oracle_pos M π μ hμ hΓ hu
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
  -- off the bad event `√q̂ ∈ [(1 − κ)√q, (1 + κ)√q]`
  have key : ∀ ω ∉ B,
      (1 - κ) * Real.sqrt q ≤ Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s') ∧
      Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s') ≤ (1 + κ) * Real.sqrt q := by
    intro ω hω
    simp only [hB, Set.mem_setOf_eq, not_exists, not_lt] at hω
    have hq1 := abs_quadForm_sub_le u _ _ hω
    have hq2 : (∑ s, |u s|) ^ 2 * r ≤ κ * q := by
      have := hell u
      rw [hκ, div_mul_eq_mul_div, le_div_iff₀ hcpos]
      nlinarith
    have h3 := abs_sqrt_sub_sqrt_le_div (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s') hqpos
    have h4 : |∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s' - q| / Real.sqrt q ≤
        κ * Real.sqrt q := by
      rw [div_le_iff₀ hsq, mul_assoc, Real.mul_self_sqrt hqpos.le]
      exact hq1.trans hq2
    have h5 := abs_le.1 (h3.trans h4)
    constructor <;> linarith [h5.1, h5.2]
  set cp : ℝ := max (z * (1 - κ)) (z * (1 + κ)) with hcp
  set cm : ℝ := min (z * (1 - κ)) (z * (1 + κ)) with hcm
  have hthr : ∀ ω ∉ B,
      cm * Real.sqrt q ≤ z * Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s') ∧
      z * Real.sqrt (∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s') ≤ cp * Real.sqrt q := by
    intro ω hω
    obtain ⟨hl, hh⟩ := key ω hω
    obtain ⟨m1, m2⟩ := mul_mem_min_max (z := z) hl hh
    rw [hcp, hcm, max_mul_of_nonneg _ _ hsq.le, min_mul_of_nonneg _ _ hsq.le]
    simp only [mul_assoc] at m1 m2 ⊢
    exact ⟨m1, m2⟩
  -- Φ at the two levels
  have hΦ : ∀ c' : ℝ, (c' = z * (1 - κ) ∨ c' = z * (1 + κ)) → |stdCDF c' - stdCDF z| ≤ κ := by
    rintro c' (h | h) <;> rw [h]
    · exact abs_stdCDF_mul_one_sub_sub_le z hκ0.le hbig
    · exact abs_stdCDF_mul_one_add_sub_le z hκ0.le
  have hΦp := hΦ cp (max_choice _ _)
  have hΦm := hΦ cm (min_choice _ _)
  -- oracle half-spaces at the two levels
  have hH : ∀ c' : ℝ, |pathProb M π μ T {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤
      c' * Real.sqrt q} - stdCDF c'| ≤ K₀ * r := by
    intro c'
    have h := hb T hT u hu c'
    rw [gaussianReal_real_Iic] at h
    exact h
  set Hp : Set (Fin T → Tuple State Action) :=
    {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤ cp * Real.sqrt q} with hHp
  set Hm : Set (Fin T → Tuple State Action) :=
    {ω | ∑ s, u s * scaledError M π η₀ V₀ ω s ≤ cm * Real.sqrt q} with hHm
  have hsub1 : E ⊆ Hp ∪ B := by
    intro ω hω
    by_cases hb' : ω ∈ B
    · exact Or.inr hb'
    · left
      have := (hthr ω hb').2
      simp only [hE, hHp, Set.mem_setOf_eq] at hω ⊢
      linarith
  have hsub2 : Hm ⊆ E ∪ B := by
    intro ω hω
    by_cases hb' : ω ∈ B
    · exact Or.inr hb'
    · left
      have := (hthr ω hb').1
      simp only [hE, hHm, Set.mem_setOf_eq] at hω ⊢
      linarith
  have hup : pathProb M π μ T E ≤ pathProb M π μ T Hp + pathProb M π μ T B :=
    (pathProb_mono M π μ T hsub1).trans (pathProb_union_le M π μ T _ _)
  have hlo : pathProb M π μ T Hm ≤ pathProb M π μ T E + pathProb M π μ T B :=
    (pathProb_mono M π μ T hsub2).trans (pathProb_union_le M π μ T _ _)
  have a1 := abs_le.1 (show |pathProb M π μ T Hp - stdCDF cp| ≤ K₀ * r from hH cp)
  have a2 := abs_le.1 (show |pathProb M π μ T Hm - stdCDF cm| ≤ K₀ * r from hH cm)
  have a3 := abs_le.1 hΦp
  have a4 := abs_le.1 hΦm
  have hB0 := pathProb_nonneg M π μ T B
  have hexp : (K₀ + C + 2 / c) * r = K₀ * r + C * r + 2 * κ := by rw [hκ]; ring
  rw [hexp]
  rw [abs_le]
  constructor
  · linarith [a2.1, a2.2, a4.1, a4.2, hPB, hlo, hκ0]
  · linarith [a1.1, a1.2, a3.1, a3.2, hPB, hup, hκ0]

/-! ## One-sided, two-sided, Bonferroni box -/

/-- **One-sided plug-in interval, rate `T^{-1/3}`.** For full-support `μ`, `Γ_true ≻ 0`,
`0 < η₀ ≤ 1` and every `V₀` there is an instance constant `K > 0` (independent of `T`, `u`, `z`)
such that for all `T ≥ 1`, `u ≠ 0`, `z ∈ ℝ`:
`|P(uᵀV̄_T − z√(uᵀΛ̂_Tu/T) ≤ uᵀV^π) − Φ(z)| ≤ K T^{-1/3}`. -/
theorem exists_abs_coverage_oneSided_plugin_sub_le [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ,
      |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | ∑ s, u s * prAverage M η₀ V₀ ω' s -
            z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') / T) ≤
            ∑ s, u s * M.valueFixedPoint π s}.indicator 1 ω -
        (gaussianReal 0 1).real (Set.Iic z)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K, hK, h⟩ :=
    exists_abs_pathProb_le_mul_sqrt_quadForm_lambdaHat_sub_le M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K, hK, fun T hT u hu z ↦ ?_⟩
  rw [sum_pathWeight_oneSided_plugin_eq M π μ η₀ V₀ hT u z]
  exact h T hT u hu z

/-- **Two-sided plug-in interval, rate `T^{-1/3}`.** Same hypotheses; one instance constant
`K > 0` (independent of `T`, `u`, `z`) such that for all `T ≥ 1`, `u ≠ 0`, `z ≥ 0`:
`|P(|uᵀ(V̄_T − V^π)| ≤ z√(uᵀΛ̂_Tu/T)) − (2Φ(z) − 1)| ≤ K T^{-1/3}`. -/
theorem exists_abs_coverage_twoSided_plugin_sub_le [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ, 0 ≤ z →
      |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action |
            |∑ s, u s * (prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s)| ≤
              z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') / T)}.indicator
            1 ω -
        (2 * (gaussianReal 0 1).real (Set.Iic z) - 1)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K, hK, h⟩ :=
    exists_abs_pathProb_le_mul_sqrt_quadForm_lambdaHat_sub_le M π μ h0 h1 V₀ hμ hΓ
  refine ⟨2 * K, by positivity, fun T hT u hu z hz ↦ ?_⟩
  rw [sum_pathWeight_twoSided_plugin_eq M π μ η₀ V₀ hT u hz]
  have hp := abs_le.1 (h T hT u hu z)
  have hm := abs_le.1 (h T hT (-u) (neg_ne_zero.2 hu) z)
  rw [abs_le]
  constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]

/-- **Bonferroni box with plug-in diagonal, rate `T^{-1/3}`.** Same hypotheses; one instance
constant `K > 0` (independent of `T`, `z`) such that for all `T ≥ 1` and `z ≥ 0`:
`P(∀ s, |V̄_T(s) − V^π(s)| ≤ z√(Λ̂_T(s,s)/T)) ≥ 1 − 2S(1 − Φ(z)) − K T^{-1/3}`. -/
theorem exists_coverage_rect_plugin_ge_sub [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ z : ℝ, 0 ≤ z →
      1 - 2 * (Fintype.card State : ℝ) * (1 - (gaussianReal 0 1).real (Set.Iic z)) -
          K * (T : ℝ) ^ (-(1 / 3 : ℝ)) ≤
        ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | ∀ s,
            |prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s| ≤
              z * Real.sqrt (lambdaHat M η₀ V₀ ω' s s / T)}.indicator 1 ω := by
  obtain ⟨K, hK, h⟩ := exists_abs_coverage_twoSided_plugin_sub_le M π μ h0 h1 V₀ hμ hΓ
  refine ⟨(Fintype.card State : ℝ) * K + 1, by positivity, fun T hT z hz ↦ ?_⟩
  set Φz := (gaussianReal 0 1).real (Set.Iic z)
  set r : ℝ := (T : ℝ) ^ (-(1 / 3 : ℝ))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let F : State → Set (Fin T → Tuple State Action) := fun s ↦
    {ω' | |∑ s₁, (Pi.single s (1 : ℝ) : State → ℝ) s₁ *
        (prAverage M η₀ V₀ ω' s₁ - M.valueFixedPoint π s₁)| ≤
      z * Real.sqrt ((∑ a, ∑ b, (Pi.single s (1 : ℝ) : State → ℝ) a *
        (Pi.single s (1 : ℝ) : State → ℝ) b * lambdaHat M η₀ V₀ ω' a b) / T)}
  have hF : ∀ s, 2 * Φz - 1 - K * r ≤ pathProb M π μ T (F s) := by
    intro s
    have h' : -(K * r) ≤ pathProb M π μ T (F s) - (2 * Φz - 1) :=
      (abs_le.1 (h T hT _ (single_one_ne_zero s) z hz)).1
    linarith
  have hsum : ∑ s, (1 - pathProb M π μ T (F s)) ≤
      (Fintype.card State : ℝ) * (2 * (1 - Φz) + K * r) := by
    calc ∑ s, (1 - pathProb M π μ T (F s)) ≤ ∑ _s : State, (2 * (1 - Φz) + K * r) :=
          sum_le_sum fun s _ ↦ by linarith [hF s]
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hfor := one_sub_sum_le_pathProb_forall M π μ T F
  have heq : pathProb M π μ T {ω | ∀ s, ω ∈ F s} =
      ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | ∀ s,
          |prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s| ≤
            z * Real.sqrt (lambdaHat M η₀ V₀ ω' s s / T)}.indicator 1 ω := by
    simp only [pathProb]
    refine sum_congr rfl fun ω _ ↦ ?_
    congr 1
    simp only [F, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, sum_single_mul,
      quadForm_single]
  rw [← heq]
  have hr' : 0 ≤ r := hr0
  nlinarith

/-! ## Combined export -/

/-- **Plug-in intervals and Bonferroni box at rate `T^{-1/3}` (`eq:convex.Cdelta`, fixed shapes,
C47(1); target `A⁻¹ diag(Γ_true) A⁻ᵀ`, C43).** For every instance with full-support `μ`,
`Γ_true ≻ 0`, `0 < η₀ ≤ 1` and every `V₀` there is one instance constant `K > 0`, depending on
`(M, π, μ, η₀, V₀)` only (not on `T`, `u`, `z`), such that for all `T ≥ 1`:
(1) for `u ≠ 0`, `z ∈ ℝ`, `|P(uᵀV̄_T − z√(uᵀΛ̂_Tu/T) ≤ uᵀV^π) − Φ(z)| ≤ K T^{-1/3}`;
(2) for `u ≠ 0`, `z ≥ 0`, `|P(|uᵀ(V̄_T − V^π)| ≤ z√(uᵀΛ̂_Tu/T)) − (2Φ(z) − 1)| ≤ K T^{-1/3}`;
(3) for `z ≥ 0`, `P(∀ s, |V̄_T(s) − V^π(s)| ≤ z√(Λ̂_T(s,s)/T)) ≥ 1 − 2S(1 − Φ(z)) − K T^{-1/3}`. -/
theorem plugin_coverage_rate [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T →
      (∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ,
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∑ s, u s * prAverage M η₀ V₀ ω' s -
              z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') / T) ≤
              ∑ s, u s * M.valueFixedPoint π s}.indicator 1 ω -
          (gaussianReal 0 1).real (Set.Iic z)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ, 0 ≤ z →
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action |
              |∑ s, u s * (prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s)| ≤
                z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') /
                  T)}.indicator 1 ω -
          (2 * (gaussianReal 0 1).real (Set.Iic z) - 1)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (∀ z : ℝ, 0 ≤ z →
        1 - 2 * (Fintype.card State : ℝ) * (1 - (gaussianReal 0 1).real (Set.Iic z)) -
            K * (T : ℝ) ^ (-(1 / 3 : ℝ)) ≤
          ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∀ s,
              |prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s| ≤
                z * Real.sqrt (lambdaHat M η₀ V₀ ω' s s / T)}.indicator 1 ω) := by
  obtain ⟨K₁, hK₁, h₁⟩ := exists_abs_coverage_oneSided_plugin_sub_le M π μ h0 h1 V₀ hμ hΓ
  obtain ⟨K₂, hK₂, h₂⟩ := exists_abs_coverage_twoSided_plugin_sub_le M π μ h0 h1 V₀ hμ hΓ
  obtain ⟨K₃, hK₃, h₃⟩ := exists_coverage_rect_plugin_ge_sub M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K₁ + K₂ + K₃, by positivity, fun T hT ↦ ⟨fun u hu z ↦ ?_, fun u hu z hz ↦ ?_,
    fun z hz ↦ ?_⟩⟩ <;>
  · have hr0 : 0 ≤ (T : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    first
    | exact (h₁ T hT u hu z).trans (by nlinarith)
    | exact (h₂ T hT u hu z hz).trans (by nlinarith)
    | exact le_trans (by nlinarith) (h₃ T hT z hz)

end StatisticalRL.Ch7Rest.TDInference

import Formalization.TDInference.PluginCovariance.Rate
import Formalization.TDInference.PluginCovariance.Rectangle
import Formalization.TDInference.Confidence.RegionsSharp

/-!
# Plug-in-covariance `ℓ∞` confidence rectangle at the rate `T^{-1/3}` (corrected C47(2))

Source: `chapters/inference.tex:198–205` (hyper-rectangles
`∏_s [V̄_T(s) − R̂/√T, V̄_T(s) + R̂/√T]` with `R̂` the `ℓ∞` quantile under the plug-in covariance),
the printed plug-in covariance `Λ̂_T = Ā_T⁻¹ Γ̂_T Ā_T⁻ᵀ` (`eq:defn-hat-Lambda`,
`inference.tex:180–182`; `lambdaHat`), and `docs/SOURCE-ISSUES.md` C47(2), C47(4), C43.

**Corrected scaling (C47(2)), not the printed formula.** As in `TDInference/PluginCovariance/Rectangle.lean`,
the half-width is `r̂_T/√T` with `r̂_T` a `(1 − α)` quantile of `‖X‖∞`, `X ~ N(0, Λ̂_T)`
(`IsSupBoxQuantile`), not the printed `R̂/√T` with `R̂` the quantile under `Λ̂_T/T` (which applies
`√T` twice). By C43 the target covariance is the corrected `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`
(`trueLambda`). On the singular event (C47(4)) Lean's junk inverse gives `Λ̂_T = 0`; that event is
inside the bad event `∃ s s', T^{-1/3} < |Λ̂_T(s,s') − Λ(s,s')|`, whose probability is charged
quantitatively, so the bound does not depend on the junk convention.

**Main result** (full-support `μ`, `0 < η₀ ≤ 1`, every `V₀`, `Γ_true ≻ 0` (added non-degeneracy
hypothesis, as for the asymptotic result), `α ∈ (0,1)`):
* `exists_coverage_rect_plugin_rate`: there is `K_α > 0` such that for **every** random level
  `r̂_T(ω)` that is, for every `T` and `ω`, a `(1 − α)` quantile of `‖·‖∞` under `N(0, Λ̂_T(ω))`,
  and every `T ≥ 1`,
  `|P(∀ s, V̄_T(s) − r̂_T/√T ≤ V^π(s) ≤ V̄_T(s) + r̂_T/√T) − (1 − α)| ≤ K_α T^{-1/3}`;
* `exists_coverage_rect_plugin_rate_quantile`: the same for `r̂_T = supBoxQuantile Λ̂_T α`.

**The constant.** `K_α` is an instance constant: it depends on `M, π, μ, η₀, V₀` and on `α`, but
not on `T` nor on the choice of the quantile `r̂`. With `ε = T^{-1/3}`,
`K_α = 2c + K₀ + C + 1/θ_α`, where `K₀` is the oracle rectangle constant
(`exists_confRegion_oracle_bounds_sharp`), `C` the consistency constant of `Λ̂_T`
(`exists_pathProb_lambdaHat_sub_gt_le`, `P(bad) ≤ C/(ε²T) = Cε`), `c = 4 gaussCmpConst/v + 1`
with `v` the sup-norm ellipticity constant of `Λ` (`quadForm_target_ge`), and
`θ_α = min(min(α, 1 − α)/(2c), v/(2S²))`. The dependence on `α` enters only through
`min(α, 1 − α)`: the sandwich uses the exact oracle levels `r∓` with `N(0,Λ)`-box mass
`1 − α ∓ 2cε`, which exist only while `2cε < min(α, 1 − α)`; for larger `ε` the bound is trivial
because `K_α ε ≥ 1`.

**No density lower bound is needed.** The levels `r∓` are chosen by mass (not by perturbing a
fixed radius), and the oracle rectangle bound `exists_confRegion_oracle_bounds_sharp` is uniform
in the radius `r`. So the error is `2cε` (the mass shift) `+ K₀ε` (oracle Berry–Esseen) `+ Cε`
(bad event), with no inverse density of the box mass near the quantile.

**Route.** (i) `abs_supBoxProb_sub_gaussCov_le`: on the good event `entryMax(Λ̂_T − Λ) ≤ ε` with
`S²ε ≤ v/2`, `Λ̂_T` is elliptic with constant `v/2` (`dotProduct_mulVec_le_entryMax`), and the
Gaussian comparison `abs_real_convex_gaussian_sub_le` (box convex, `convex_supBox`) gives
`|N(0,Λ̂_T)(box_r) − N(0,Λ)(box_r)| ≤ (2 gaussCmpConst/v) ε` uniformly in `r`. (ii) The
quantile property forces `r⁻ ≤ r̂_T ≤ r⁺` on the good event. (iii) Oracle rectangle bounds at
`r⁻, r⁺` and the bad-event probability.

Not covered: the printed (double-`√T`) scaling, data-selected convex sets (C47(1)).
-/

open MeasureTheory ProbabilityTheory Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Probability.GaussianConvexCompare

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-- `ε = T^{-1/3}` satisfies `ε³ T = 1`. -/
theorem rpow_neg_third_pow_three_mul_self {T : ℕ} (hT : 1 ≤ T) :
    ((T : ℝ) ^ (-(1 / 3 : ℝ))) ^ 3 * T = 1 := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

omit [DecidableEq State] in
/-- **Uniform Gaussian box comparison on the good event** (infrastructure). Let `Λ = L Lᵀ` with
sup-norm ellipticity `v ‖u‖² ≤ uᵀ Λ u` (`v > 0`), and let `Σ` be PSD with
`|Σ(i,j) − Λ(i,j)| ≤ ε` for all `i, j` and `S² ε ≤ v/2` (`S = card State`). Then for every `r`,
`|N(0,Σ){‖x‖∞ ≤ r} − N(0,Λ){‖x‖∞ ≤ r}| ≤ (2 gaussCmpConst / v) ε`. -/
theorem abs_supBoxProb_sub_map_le (L : Matrix State State ℝ) {v : ℝ} (hv : 0 < v)
    (hL : ∀ u : State → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L * Lᵀ) *ᵥ u)) {Sg : Matrix State State ℝ}
    (hSg : Sg.PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) (hclose : ∀ i j, |Sg i j - (L * Lᵀ) i j| ≤ ε)
    (hsmall : (Fintype.card State : ℝ) ^ 2 * ε ≤ v / 2) (r : ℝ) :
    |supBoxProb Sg r - ((stdGaussianPi State).map (L *ᵥ ·)).real {x | ∀ s, |x s| ≤ r}| ≤
      2 * gaussCmpConst State / v * ε := by
  obtain ⟨Q, hQ⟩ := exists_mul_transpose_eq_of_posSemidef hSg
  have hG : gaussOfCov Sg = (stdGaussianPi State).map (Q *ᵥ ·) := gaussOfCov_eq_map hSg Q hQ
  have hem : entryMax (L * Lᵀ - Sg) ≤ ε :=
    Real.iSup_le (fun p ↦ by rw [sub_apply, abs_sub_comm]; exact hclose p.1 p.2) hε
  have hem' : entryMax (Q * Qᵀ - L * Lᵀ) ≤ ε :=
    Real.iSup_le (fun p ↦ by rw [sub_apply, hQ]; exact hclose p.1 p.2) hε
  have hv2 : 0 < v / 2 := by positivity
  have h₂ : ∀ u : State → ℝ, v / 2 * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L * Lᵀ) *ᵥ u) := fun u ↦
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity)).trans (hL u)
  have h₁ : ∀ u : State → ℝ, v / 2 * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((Q * Qᵀ) *ᵥ u) := by
    intro u
    have hsq : ∑ i, u i * u i ≤ (Fintype.card State : ℝ) * ‖u‖ ^ 2 := by
      have hi : ∀ i ∈ (univ : Finset State), u i * u i ≤ ‖u‖ ^ 2 := fun i _ ↦ by
        have := norm_le_pi_norm u i
        rw [Real.norm_eq_abs] at this
        nlinarith [abs_nonneg (u i), abs_mul_abs_self (u i)]
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hi
    have hd := dotProduct_mulVec_le_entryMax (L * Lᵀ - Sg) u
    have hsplit : u ⬝ᵥ ((Q * Qᵀ) *ᵥ u) =
        u ⬝ᵥ ((L * Lᵀ) *ᵥ u) - u ⬝ᵥ ((L * Lᵀ - Sg) *ᵥ u) := by
      rw [hQ, sub_mulVec, dotProduct_sub]; ring
    have hS0 : (0 : ℝ) ≤ Fintype.card State := Nat.cast_nonneg _
    have hb : (Fintype.card State : ℝ) * entryMax (L * Lᵀ - Sg) * ∑ i, u i * u i ≤
        (Fintype.card State : ℝ) ^ 2 * ε * ‖u‖ ^ 2 := by
      have hsum0 : 0 ≤ ∑ i, u i * u i := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
      calc (Fintype.card State : ℝ) * entryMax (L * Lᵀ - Sg) * ∑ i, u i * u i
          ≤ (Fintype.card State : ℝ) * ε * ∑ i, u i * u i := by gcongr
        _ ≤ (Fintype.card State : ℝ) * ε * ((Fintype.card State : ℝ) * ‖u‖ ^ 2) := by gcongr
        _ = _ := by ring
    have hc : (Fintype.card State : ℝ) ^ 2 * ε * ‖u‖ ^ 2 ≤ v / 2 * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    have := hL u
    rw [hsplit]
    nlinarith
  have hcmp := abs_real_convex_gaussian_sub_le Q L hv2 h₁ h₂ (convex_supBox r)
  rw [supBoxProb, hG]
  refine hcmp.trans ?_
  have hc0 : 0 ≤ gaussCmpConst State / (v / 2) := div_nonneg (gaussCmpConst_nonneg) hv2.le
  calc gaussCmpConst State / (v / 2) * entryMax (Q * Qᵀ - L * Lᵀ)
      ≤ gaussCmpConst State / (v / 2) * ε := mul_le_mul_of_nonneg_left hem' hc0
    _ = 2 * gaussCmpConst State / v * ε := by field_simp

/-- **Plug-in `ℓ∞` confidence rectangle at the rate `T^{-1/3}` (corrected C47(2)).** For
full-support `μ`, `0 < η₀ ≤ 1`, every `V₀`, `Γ_true ≻ 0` and `α ∈ (0,1)` there is an instance
constant `K_α > 0` (depending on `M, π, μ, η₀, V₀` and on `α` through `min(α, 1 − α)`; independent
of `T` and of the quantile choice) such that: for every random level `r̂_T(ω)` that is, for every
`T` and every outcome `ω`, a `(1 − α)` quantile of `‖X‖∞` for `X ~ N(0, Λ̂_T(ω))`
(`IsSupBoxQuantile`), with the printed plug-in `Λ̂_T = Ā_T⁻¹ Γ̂_T Ā_T⁻ᵀ` (`lambdaHat`), and every
`T ≥ 1`,
`|P(∀ s, V̄_T(s) − r̂_T/√T ≤ V^π(s) ≤ V̄_T(s) + r̂_T/√T) − (1 − α)| ≤ K_α T^{-1/3}`.
Source: `inference.tex:198–205`, `eq:defn-hat-Lambda` `inference.tex:180–182`. Corrected scaling
per C47(2): half-width `r̂_T/√T` with `r̂_T` the quantile under `Λ̂_T`, not the printed `R̂/√T`.
Junk value on the singular event per C47(4); target covariance `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` per C43. -/
theorem exists_coverage_rect_plugin_rate [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) (hμ : ∀ s, 0 < μ.prob s)
    (hΓ : ∀ s, 0 < trueGamma M π μ s) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ rhat : (T : ℕ) → (Fin T → Tuple State Action) → ℝ,
      (∀ (T : ℕ) (ω : Fin T → Tuple State Action),
        IsSupBoxQuantile (lambdaHat M η₀ V₀ ω) α (rhat T ω)) →
      ∀ T : ℕ, 1 ≤ T →
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∀ s,
              prAverage M η₀ V₀ ω' s - rhat T ω' / Real.sqrt T ≤ M.valueFixedPoint π s ∧
                M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + rhat T ω' / Real.sqrt T}.indicator
              1 ω - (1 - α)| ≤
          K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨K₀, hK₀, hb⟩ := exists_confRegion_oracle_bounds_sharp M π μ h0 h1 V₀ hμ hΓ
  obtain ⟨C, hC, hcons⟩ := exists_pathProb_lambdaHat_sub_gt_le M π μ hμ h0 h1 V₀
  set A := tdA M π μ with hAdef
  set L : Matrix State State ℝ := gaussCovFactor A (trueGamma M π μ) with hLdef
  have hLL : L * Lᵀ = trueLambda M π μ :=
    gaussCovFactor_mul_transpose _ fun s ↦ (hΓ s).le
  have hGL : ∀ r : ℝ, (gaussCov A (trueGamma M π μ)).real {x | ∀ s, |x s| ≤ r} =
      ((stdGaussianPi State).map (L *ᵥ ·)).real {x | ∀ s, |x s| ≤ r} := fun r ↦ by
    rw [gaussCov_eq_map_mulVec]
  have hA : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ
      (μmin := Finset.univ.inf' Finset.univ_nonempty μ.prob)
      ((Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s) (fun s ↦ Finset.inf'_le _ (mem_univ s)))
  -- sup-norm ellipticity of `Λ`
  set g : ℝ := Finset.univ.inf' Finset.univ_nonempty (trueGamma M π μ) with hgdef
  have hg0 : 0 < g := (Finset.lt_inf'_iff _).2 fun s _ ↦ hΓ s
  have hg : ∀ r, g ≤ trueGamma M π μ r := fun r ↦ Finset.inf'_le _ (mem_univ r)
  set v : ℝ := g / ((Fintype.card State : ℝ) * (∑ r, ∑ s, |A r s|) ^ 2 + 1) with hvdef
  have hv : 0 < v := by positivity
  have hLv : ∀ u : State → ℝ, v * ‖u‖ ^ 2 ≤ u ⬝ᵥ ((L * Lᵀ) *ᵥ u) := fun u ↦ by
    rw [hLL]; exact quadForm_target_ge A hA _ hg0.le hg u
  -- constants
  set S : ℝ := (Fintype.card State : ℝ) with hSdef
  have hS1 : 1 ≤ S := by rw [hSdef]; exact_mod_cast Fintype.card_pos
  set c : ℝ := 4 * gaussCmpConst State / v + 1 with hcdef
  have hc0 : 0 < c := by have := gaussCmpConst_nonneg (ι := State); positivity
  set m : ℝ := min α (1 - α) with hmdef
  have hm0 : 0 < m := lt_min hα0 (by linarith)
  have hmα : m ≤ α := min_le_left _ _
  have hm1 : m ≤ 1 - α := min_le_right _ _
  set θ : ℝ := min (m / (2 * c)) (v / (2 * S ^ 2)) with hθdef
  have hθ0 : 0 < θ := lt_min (by positivity) (by positivity)
  refine ⟨2 * c + K₀ + C + 1 / θ, by positivity, fun rhat hrhat T hT ↦ ?_⟩
  set ε : ℝ := (T : ℝ) ^ (-(1 / 3 : ℝ)) with hεdef
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hT0 _
  have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT) (by norm_num)
  have hε3 : ε ^ 3 * T = 1 := rpow_neg_third_pow_three_mul_self hT
  -- the coverage probability lies in `[0, 1]`
  set Eh : Set (Fin T → Tuple State Action) := {ω' | ∀ s,
      prAverage M η₀ V₀ ω' s - rhat T ω' / Real.sqrt T ≤ M.valueFixedPoint π s ∧
        M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + rhat T ω' / Real.sqrt T} with hEhdef
  change |pathProb M π μ T Eh - (1 - α)| ≤ _
  have hP0 : 0 ≤ pathProb M π μ T Eh := pathProb_nonneg M π μ T Eh
  have hP1 : pathProb M π μ T Eh ≤ 1 :=
    (pathProb_mono M π μ T (Set.subset_univ Eh)).trans_eq (pathProb_univ M π μ T)
  have hrest : 0 ≤ (2 * c + K₀ + C) * ε := by positivity
  have hKε : (2 * c + K₀ + C + 1 / θ) * ε = (2 * c + K₀ + C) * ε + ε / θ := by ring
  by_cases hsmall : 2 * c * ε < m ∧ S ^ 2 * ε ≤ v / 2
  swap
  · -- large `ε`: the bound is trivial
    have hθε : θ ≤ ε := by
      rcases not_and_or.1 hsmall with h | h
      · refine (min_le_left _ _).trans ?_
        rw [div_le_iff₀ (by positivity)]; linarith
      · refine (min_le_right _ _).trans ?_
        rw [div_le_iff₀ (by positivity)]; linarith
    have h1 : 1 ≤ ε / θ := by rw [le_div_iff₀ hθ0]; linarith
    rw [hKε, abs_le]
    constructor <;> linarith
  obtain ⟨h2cε, hSε⟩ := hsmall
  set ρ : ℝ := c * ε with hρdef
  have hρ0 : 0 < ρ := by positivity
  -- exact oracle levels with masses `1 − α ∓ 2ρ`
  obtain ⟨rm, -, hrm⟩ := exists_supBox_level_eq M π μ hμ hΓ (α := α + 2 * ρ) (by positivity)
    (by linarith)
  obtain ⟨rp, -, hrp⟩ := exists_supBox_level_eq M π μ hμ hΓ (α := α - 2 * ρ) (by linarith)
    (by linarith)
  -- bad event
  set B : Set (Fin T → Tuple State Action) :=
    {ω | ∃ s s', ε < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|} with hBdef
  have hPB : pathProb M π μ T B ≤ C * ε := by
    refine (hcons T hT ε hε0 hε1).trans_eq ?_
    have hε2 : ε ^ 2 * T = ε⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← hε3]; ring)
    rw [hε2, div_inv_eq_mul]
  have hB0 : 0 ≤ pathProb M π μ T B := pathProb_nonneg M π μ T B
  -- on the good event, `rm ≤ r̂_T ≤ rp`
  have hcmpρ : 2 * gaussCmpConst State / v * ε ≤ ρ := by
    rw [hρdef, hcdef]
    have : 2 * gaussCmpConst State / v ≤ 4 * gaussCmpConst State / v + 1 := by
      have := gaussCmpConst_nonneg (ι := State)
      have h2 : 2 * gaussCmpConst State / v ≤ 4 * gaussCmpConst State / v := by
        gcongr; norm_num
      linarith
    exact mul_le_mul_of_nonneg_right this hε0.le
  have hgood : ∀ ω : Fin T → Tuple State Action, ω ∉ B → rm ≤ rhat T ω ∧ rhat T ω ≤ rp := by
    intro ω hω
    simp only [hBdef, Set.mem_setOf_eq, not_exists, not_lt] at hω
    have hcl : ∀ i j, |lambdaHat M η₀ V₀ ω i j - (L * Lᵀ) i j| ≤ ε := fun i j ↦ by
      rw [hLL]; exact hω i j
    have hcmp : ∀ r, |supBoxProb (lambdaHat M η₀ V₀ ω) r -
        (gaussCov A (trueGamma M π μ)).real {x | ∀ s, |x s| ≤ r}| ≤ ρ := fun r ↦ by
      rw [hGL]
      exact (abs_supBoxProb_sub_map_le L hv hLv (posSemidef_lambdaHat M η₀ V₀ ω) hε0.le hcl
        hSε r).trans hcmpρ
    have hm := hcmp rm
    have hp := hcmp rp
    rw [hrm] at hm
    rw [hrp] at hp
    obtain ⟨hq1, hq2⟩ := hrhat T ω
    exact ⟨hq1 rm (by linarith [(abs_le.1 hm).2]), hq2 rp (by linarith [(abs_le.1 hp).1])⟩
  -- the sandwich
  let Ev : ℝ → Set (Fin T → Tuple State Action) := fun r ↦
    {ω' | ∀ s, prAverage M η₀ V₀ ω' s - r / Real.sqrt T ≤ M.valueFixedPoint π s ∧
      M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + r / Real.sqrt T}
  have hsub1 : Eh ⊆ Ev rp ∪ B := by
    intro ω hω
    by_cases hb' : ω ∈ B
    · exact Or.inr hb'
    · left
      have hle : rhat T ω / Real.sqrt T ≤ rp / Real.sqrt T := by
        gcongr; exact (hgood ω hb').2
      intro s
      obtain ⟨h1', h2'⟩ := hω s
      exact ⟨by linarith, by linarith⟩
  have hsub2 : Ev rm ⊆ Eh ∪ B := by
    intro ω hω
    by_cases hb' : ω ∈ B
    · exact Or.inr hb'
    · left
      have hle : rm / Real.sqrt T ≤ rhat T ω / Real.sqrt T := by
        gcongr; exact (hgood ω hb').1
      intro s
      obtain ⟨h1', h2'⟩ := hω s
      exact ⟨by linarith, by linarith⟩
  have hup : pathProb M π μ T Eh ≤ pathProb M π μ T (Ev rp) + pathProb M π μ T B :=
    (pathProb_mono M π μ T hsub1).trans (pathProb_union_le M π μ T _ _)
  have hlo : pathProb M π μ T (Ev rm) ≤ pathProb M π μ T Eh + pathProb M π μ T B :=
    (pathProb_mono M π μ T hsub2).trans (pathProb_union_le M π μ T _ _)
  -- oracle rectangle bounds at `rm, rp`
  have hom : |pathProb M π μ T (Ev rm) - (1 - (α + 2 * ρ))| ≤ K₀ * ε := by
    rw [← hrm]; exact (hb T hT).2.2 rm
  have hop : |pathProb M π μ T (Ev rp) - (1 - (α - 2 * ρ))| ≤ K₀ * ε := by
    rw [← hrp]; exact (hb T hT).2.2 rp
  have a1 := abs_le.1 hom
  have a2 := abs_le.1 hop
  have hθε : 0 ≤ ε / θ := by positivity
  rw [hKε, abs_le]
  constructor <;> linarith

/-- **Plug-in `ℓ∞` rectangle with the concrete lower quantile, rate `T^{-1/3}` (corrected
C47(2)).** Same hypotheses as `exists_coverage_rect_plugin_rate`, with
`r̂_T(ω) = supBoxQuantile Λ̂_T(ω) α = inf {r | N(0, Λ̂_T(ω)){‖x‖∞ ≤ r} ≥ 1 − α}` for the printed
plug-in `Λ̂_T`: there is an instance constant `K_α > 0` (depending on `α`) with, for all `T ≥ 1`,
`|P(∀ s, V̄_T(s) − r̂_T/√T ≤ V^π(s) ≤ V̄_T(s) + r̂_T/√T) − (1 − α)| ≤ K_α T^{-1/3}`.
Source: `inference.tex:198–205`, `eq:defn-hat-Lambda` :180–182; corrected scaling per C47(2);
C47(4), C43. -/
theorem exists_coverage_rect_plugin_rate_quantile [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T →
      |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | ∀ s,
            prAverage M η₀ V₀ ω' s - supBoxQuantile (lambdaHat M η₀ V₀ ω') α / Real.sqrt T ≤
                M.valueFixedPoint π s ∧
              M.valueFixedPoint π s ≤
                prAverage M η₀ V₀ ω' s + supBoxQuantile (lambdaHat M η₀ V₀ ω') α / Real.sqrt T}.indicator
            1 ω - (1 - α)| ≤
        K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K, hK, h⟩ := exists_coverage_rect_plugin_rate M π μ h0 h1 V₀ hμ hΓ hα0 hα1
  exact ⟨K, hK, h (fun _ ω ↦ supBoxQuantile (lambdaHat M η₀ V₀ ω) α)
    (fun _ _ ↦ isSupBoxQuantile_supBoxQuantile _ hα0 hα1)⟩

end StatisticalRL.Ch7Rest.TDInference

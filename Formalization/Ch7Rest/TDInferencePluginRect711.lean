import Formalization.Ch7Rest.TDInferencePluginRegion711

/-!
# Plug-in-covariance confidence rectangle: asymptotic coverage `1 − α` (corrected C47(2))

Source: `chapters/inference.tex:198–205` (hyper-rectangles
`∏_s [V̄_T(s) − R̂/√T, V̄_T(s) + R̂/√T]`, "`R̂ > 0` is the (random) quantile of the `ℓ∞` norm of a
centered Gaussian random vector with covariance `Λ̂_T/T`"), the plug-in covariance
`eq:defn-hat-Lambda` (`inference.tex:180–182`), and `docs/SOURCE-ISSUES.md` C47(2), C47(4), C43.

**Corrected scaling (C47(2)), not the printed formula.** The printed half-width `R̂/√T` with `R̂` the
quantile under `Λ̂_T/T` applies `√T` twice (half-width `O(1/T)`, coverage `→ 0`). Here the
half-width is `r̂_T/√T` with `r̂_T` a `(1 − α)` quantile of `‖X‖∞` for `X ~ N(0, Λ̂_T)`;
with `R̂` the quantile under `Λ̂_T/T` one has `R̂ = r̂_T/√T` (Gaussian scaling; paper fact, not formalized), so the half-width is `R̂`.

**The Gaussian `N(0, Σ)` for a matrix `Σ` (`gaussOfCov`).** For a real positive semidefinite `Σ`,
`N(0, Σ)` is the law of `Q Z` with `Z` standard Gaussian on `ι → ℝ` and `Q` a (choice of) square
factor `Q Qᵀ = Σ` (`exists_mul_transpose_eq_of_posSemidef`); the law does not depend on the factor
(`map_mulVec_stdGaussianPi_eq`). For non-PSD `Σ` the convention is the point mass at `0`; it is never
used here, because the printed `Λ̂_T` is always PSD (`posSemidef_lambdaHat`, also with Lean's junk
inverse on the singular event of C47(4), where `Λ̂_T = 0` and `N(0,0)` is the point mass at `0`).

**Quantiles.** `supBoxProb Σ r = N(0,Σ){x | ∀ i, |x i| ≤ r}`. A real `r̂` is a `(1 − α)`
quantile (`IsSupBoxQuantile Σ α r̂`) when `supBoxProb Σ r < 1 − α → r ≤ r̂` and
`1 − α < supBoxProb Σ r → r̂ ≤ r` for all `r` (any point of the quantile interval). Every exact level
(`supBoxProb Σ r̂ = 1 − α`) is one (`isSupBoxQuantile_of_eq`), and the concrete lower quantile
`supBoxQuantile Σ α = sInf {r | 1 − α ≤ supBoxProb Σ r}` is one for `α ∈ (0,1)`
(`isSupBoxQuantile_supBoxQuantile`).

**Main results** (full-support `μ`, `0 < η₀ ≤ 1` (containing the printed `(0, 1/4)`), every `V₀`,
`Γ_true ≻ 0` (added non-degeneracy hypothesis), `α ∈ (0,1)`):
* `tendsto_coverage_rect_plugin`: for **every** random level `r̂_T(ω)` that is, for every `T` and
  every outcome `ω`, a `(1 − α)` quantile of `‖·‖∞` under `N(0, Λ̂_T(ω))`,
  `P(∀ s, V̄_T(s) − r̂_T/√T ≤ V^π(s) ≤ V̄_T(s) + r̂_T/√T) → 1 − α`;
* `tendsto_coverage_rect_plugin_quantile`: the same for the concrete `r̂_T = supBoxQuantile Λ̂_T α`.
The quantile property is the definition of the level, not an extra probabilistic assumption: no
convergence of `r̂_T` is assumed. By C43 the limit covariance is the corrected
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (`trueLambda`).

**Asymptotic only in this file** (the finite-`T` rate is in `TDInferencePluginRectRate711.lean`). The consistency of `Λ̂_T` (`eq_defn_hat_Lambda_corrected`) has no rate, so this
is a limit statement; no finite-`T` rate is claimed.

**Route.** (i) Continuity of `Σ ↦ N(0,Σ){‖x‖∞ ≤ r}` at `Λ = L Lᵀ` (`L` invertible) among PSD `Σ`
(`exists_delta_abs_supBoxProb_sub_lt`): if `Σ` is entrywise `δ`-close to `Λ`, then
`Σ − (1 − κ)Λ` is PSD (as `xᵀΛx ≥ c (∑|x_i|)²`), so `Σ = F Fᵀ` with the rectangular factor
`F = [√(1−κ) L | Q]`, `Q Qᵀ = Σ − (1 − κ)Λ`, whose entries are close to those of `[L | 0]`; dominated
convergence along `F → [L | 0]` (`exists_delta_abs_map_mulVec_real_sub_lt`), using that the box
frontier is `N(0,Λ)`-null. (ii) Exact oracle levels `r⁻, r⁺` with `N(0,Λ)`-mass `1 − α ∓ ν`
(`exists_supBox_level_eq`); on the good event `Λ̂_T ≈ Λ`, monotonicity of the `N(0,Λ̂_T)` box mass
forces `r⁻ ≤ r̂_T ≤ r⁺`. (iii) The oracle rectangle bounds (`exists_confRegion_oracle_bounds`) at
`r⁻, r⁺` and the bad-event probability `→ 0`.

Not covered: any rate for the plug-in rectangle, the printed (double-`√T`) scaling, data-selected
convex sets (C47(1)).
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability

/-! ## The centred Gaussian with a given PSD covariance and its `ℓ∞` box masses -/

section Generic

variable {ι : Type} [Fintype ι]

/-- `N(0, Σ)` on `ι → ℝ`: for PSD `Σ`, the law of `Q Z` with `Z` standard Gaussian and `Q` a chosen
square factor with `Q Qᵀ = Σ` (the law does not depend on the factor, `map_mulVec_stdGaussianPi_eq`);
for non-PSD `Σ`, by convention, the point mass at `0`. -/
noncomputable def gaussOfCov (S : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  open Classical in
  if h : S.PosSemidef then
    (stdGaussianPi ι).map ((exists_mul_transpose_eq_of_posSemidef h).choose *ᵥ ·)
  else Measure.dirac 0

instance isProbabilityMeasure_gaussOfCov (S : Matrix ι ι ℝ) :
    IsProbabilityMeasure (gaussOfCov S) := by
  unfold gaussOfCov
  split
  · exact Measure.isProbabilityMeasure_map
      (Continuous.matrix_mulVec continuous_const continuous_id).measurable.aemeasurable
  · infer_instance

/-- For PSD `Σ` and any factor `F` (any finite column type) with `F Fᵀ = Σ`,
`N(0, Σ)` is the law of `F Z`. -/
theorem gaussOfCov_eq_map {κ : Type} [Fintype κ] {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (F : Matrix ι κ ℝ) (hF : F * Fᵀ = S) :
    gaussOfCov S = (stdGaussianPi κ).map (F *ᵥ ·) := by
  rw [gaussOfCov, dif_pos hS]
  exact map_mulVec_stdGaussianPi_eq _ _
    ((exists_mul_transpose_eq_of_posSemidef hS).choose_spec.trans hF.symm)

/-- `N(0, Σ){x | ∀ i, |x i| ≤ r}`, the `ℓ∞` box mass (the cdf of `‖X‖∞`, `X ~ N(0, Σ)`). -/
noncomputable def supBoxProb (S : Matrix ι ι ℝ) (r : ℝ) : ℝ :=
  (gaussOfCov S).real {x | ∀ i, |x i| ≤ r}

/-- `r̂` is a `(1 − α)` quantile of `‖X‖∞`, `X ~ N(0, Σ)`: every `r` with box mass `< 1 − α` lies
below `r̂`, every `r` with box mass `> 1 − α` lies above. -/
def IsSupBoxQuantile (S : Matrix ι ι ℝ) (α r : ℝ) : Prop :=
  (∀ r', supBoxProb S r' < 1 - α → r' ≤ r) ∧ (∀ r', 1 - α < supBoxProb S r' → r ≤ r')

/-- The lower `(1 − α)` quantile `inf {r | N(0,Σ){‖x‖∞ ≤ r} ≥ 1 − α}`. -/
noncomputable def supBoxQuantile (S : Matrix ι ι ℝ) (α : ℝ) : ℝ :=
  sInf {r | 1 - α ≤ supBoxProb S r}

theorem measurableSet_supBox (r : ℝ) : MeasurableSet {x : ι → ℝ | ∀ i, |x i| ≤ r} := by
  have h : {x : ι → ℝ | ∀ i, |x i| ≤ r} = ⋂ i, {x : ι → ℝ | |x i| ≤ r} := by
    ext x; simp
  rw [h]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le (by fun_prop) measurable_const

theorem supBoxProb_mono (S : Matrix ι ι ℝ) {r r' : ℝ} (h : r ≤ r') :
    supBoxProb S r ≤ supBoxProb S r' :=
  measureReal_mono (fun _ hx i ↦ (hx i).trans h) (measure_ne_top _ _)

/-- Every exact level is a quantile. -/
theorem isSupBoxQuantile_of_eq (S : Matrix ι ι ℝ) {α r : ℝ} (hr : supBoxProb S r = 1 - α) :
    IsSupBoxQuantile S α r := by
  refine ⟨fun r' hr' ↦ ?_, fun r' hr' ↦ ?_⟩
  · by_contra h
    have := supBoxProb_mono S (not_le.1 h).le
    linarith
  · by_contra h
    have := supBoxProb_mono S (not_le.1 h).le
    linarith

theorem supBoxProb_of_neg [Nonempty ι] (S : Matrix ι ι ℝ) {r : ℝ} (hr : r < 0) :
    supBoxProb S r = 0 := by
  have h : {x : ι → ℝ | ∀ i, |x i| ≤ r} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_le]
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨i, hr.trans_le (abs_nonneg _)⟩
  rw [supBoxProb, h, measureReal_empty]

theorem exists_nat_lt_supBoxProb (S : Matrix ι ι ℝ) {p : ℝ} (hp : p < 1) :
    ∃ n : ℕ, p < supBoxProb S n := by
  have hmono : Monotone fun n : ℕ ↦ {x : ι → ℝ | ∀ i, |x i| ≤ n} := fun m n hmn x hx i ↦
    (hx i).trans (by exact_mod_cast hmn)
  have hU : (⋃ n : ℕ, {x : ι → ℝ | ∀ i, |x i| ≤ n}) = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (∑ i, |x i|)
    refine Set.mem_iUnion.2 ⟨n, fun i ↦ ?_⟩
    exact (single_le_sum (f := fun i ↦ |x i|) (fun _ _ ↦ abs_nonneg _) (mem_univ i)).trans hn
  have ht := tendsto_measure_iUnion_atTop (μ := gaussOfCov S) hmono
  rw [hU, measure_univ] at ht
  have ht' : Tendsto (fun n : ℕ ↦ supBoxProb S n) atTop (𝓝 1) := by
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp ht
    simpa [supBoxProb, measureReal_def, Function.comp_def] using this
  exact (ht'.eventually (lt_mem_nhds hp)).exists

/-- The concrete lower quantile `supBoxQuantile Σ α` is a `(1 − α)` quantile for `α ∈ (0,1)`. -/
theorem isSupBoxQuantile_supBoxQuantile [Nonempty ι] (S : Matrix ι ι ℝ) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) : IsSupBoxQuantile S α (supBoxQuantile S α) := by
  set A : Set ℝ := {r | 1 - α ≤ supBoxProb S r} with hA
  obtain ⟨n, hn⟩ := exists_nat_lt_supBoxProb S (by linarith : 1 - α < 1)
  have hne : A.Nonempty := ⟨n, hn.le⟩
  have hbdd : BddBelow A := ⟨0, fun r hr ↦ by
    by_contra h
    have := supBoxProb_of_neg S (not_le.1 h)
    have hr' : 1 - α ≤ supBoxProb S r := hr
    linarith⟩
  refine ⟨fun r' hr' ↦ le_csInf hne fun b hb ↦ ?_, fun r' hr' ↦ csInf_le hbdd hr'.le⟩
  by_contra h
  have := supBoxProb_mono S (not_le.1 h).le
  have hb' : 1 - α ≤ supBoxProb S b := hb
  linarith

theorem dotProduct_mulVec_eq_sum (P : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (P *ᵥ x) = ∑ i, ∑ j, x i * x j * P i j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

theorem quadForm_mul_transpose {κ : Type} [Fintype κ] (L : Matrix ι κ ℝ) (x : ι → ℝ) :
    ∑ i, ∑ j, x i * x j * (L * Lᵀ) i j = ∑ k, (∑ i, x i * L i k) ^ 2 := by
  calc _ = ∑ i, ∑ j, ∑ k, x i * L i k * (x j * L j k) := by
        refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
        rw [Matrix.mul_apply, Finset.mul_sum]
        exact sum_congr rfl fun k _ ↦ by rw [transpose_apply]; ring
    _ = ∑ i, ∑ k, ∑ j, x i * L i k * (x j * L j k) := sum_congr rfl fun i _ ↦ Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, x i * L i k * (x j * L j k) := Finset.sum_comm
    _ = _ := sum_congr rfl fun k _ ↦ by rw [sq, Finset.sum_mul_sum]

/-- **Continuity of `F ↦ P(F Z ∈ E)` at `F₀`** when the frontier of `E` is null for the law of
`F₀ Z` (dominated convergence; `Z` standard Gaussian). -/
theorem exists_delta_abs_map_mulVec_real_sub_lt {κ : Type} [Fintype κ] (F₀ : Matrix ι κ ℝ)
    {E : Set (ι → ℝ)} (hE : MeasurableSet E)
    (hnull : ((stdGaussianPi κ).map (F₀ *ᵥ ·)) (frontier E) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : Matrix ι κ ℝ, (∀ i j, |F i j - F₀ i j| < δ) →
      |((stdGaussianPi κ).map (F *ᵥ ·)).real E - ((stdGaussianPi κ).map (F₀ *ᵥ ·)).real E| < ε := by
  set γ := stdGaussianPi κ with hγ
  have hm : ∀ F : Matrix ι κ ℝ, Measurable (F *ᵥ · : (κ → ℝ) → ι → ℝ) := fun F ↦
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hrepr : ∀ F : Matrix ι κ ℝ, (γ.map (F *ᵥ ·)).real E =
      ∫ z, ((F *ᵥ ·) ⁻¹' E).indicator (1 : (κ → ℝ) → ℝ) z ∂γ := fun F ↦ by
    rw [map_measureReal_apply (hm F) hE, integral_indicator_one (hm F hE)]
  have hlim : Tendsto (fun F : ι → κ → ℝ ↦
      ∫ z, ((Matrix.of F *ᵥ ·) ⁻¹' E).indicator (1 : (κ → ℝ) → ℝ) z ∂γ)
      (𝓝 (F₀ : ι → κ → ℝ)) (𝓝 (∫ z, ((F₀ *ᵥ ·) ⁻¹' E).indicator (1 : (κ → ℝ) → ℝ) z ∂γ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ)) ?_ ?_
      (integrable_const 1) ?_
    · exact Eventually.of_forall fun F ↦
        (measurable_const.indicator (hm (Matrix.of F) hE)).aestronglyMeasurable
    · refine Eventually.of_forall fun F ↦ Eventually.of_forall fun z ↦ ?_
      by_cases h : z ∈ (Matrix.of F *ᵥ ·) ⁻¹' E <;> simp [Set.indicator, h]
    · have hz : ∀ᵐ z ∂γ, F₀ *ᵥ z ∉ frontier E := by
        rw [ae_iff]
        simp only [not_not]
        have h := hnull
        rw [Measure.map_apply (hm F₀) isClosed_frontier.measurableSet] at h
        exact h
      filter_upwards [hz] with z hz
      have hfun : (fun F : ι → κ → ℝ ↦ Matrix.of F *ᵥ z) = fun F i ↦ ∑ j, F i j * z j := by
        funext F i; rfl
      have hc : Continuous fun F : ι → κ → ℝ ↦ Matrix.of F *ᵥ z := by
        rw [hfun]; fun_prop
      have hc' : Tendsto (fun F : ι → κ → ℝ ↦ Matrix.of F *ᵥ z) (𝓝 (F₀ : ι → κ → ℝ))
          (𝓝 (F₀ *ᵥ z)) := hc.tendsto _
      by_cases hint : F₀ *ᵥ z ∈ interior E
      · have hev := hc'.eventually (isOpen_interior.mem_nhds hint)
        have hF₀E : z ∈ (F₀ *ᵥ ·) ⁻¹' E := show F₀ *ᵥ z ∈ E from interior_subset hint
        refine tendsto_const_nhds.congr' (hev.mono fun F hF ↦ ?_)
        have hFE : z ∈ (Matrix.of F *ᵥ ·) ⁻¹' E :=
          show Matrix.of F *ᵥ z ∈ E from interior_subset hF
        dsimp only
        rw [Set.indicator_of_mem hF₀E, Set.indicator_of_mem hFE]
      · have hcl : F₀ *ᵥ z ∉ closure E := fun hcl ↦ hz ⟨hcl, hint⟩
        have hev := hc'.eventually (isClosed_closure.isOpen_compl.mem_nhds hcl)
        have hF₀E : z ∉ (F₀ *ᵥ ·) ⁻¹' E := fun h ↦ hcl (subset_closure h)
        refine tendsto_const_nhds.congr' (hev.mono fun F hF ↦ ?_)
        have hFE : z ∉ (Matrix.of F *ᵥ ·) ⁻¹' E := fun h ↦ hF (subset_closure h)
        dsimp only
        rw [Set.indicator_of_notMem hF₀E, Set.indicator_of_notMem hFE]
  obtain ⟨δ, hδ, hball⟩ := Metric.tendsto_nhds_nhds.1 hlim ε hε
  refine ⟨δ, hδ, fun F hF ↦ ?_⟩
  have hd : dist (Matrix.of.symm F) (Matrix.of.symm F₀) < δ :=
    (dist_pi_lt_iff hδ).2 fun i ↦ (dist_pi_lt_iff hδ).2 fun j ↦ by
      rw [Real.dist_eq]; exact hF i j
  have h := hball hd
  rw [Real.dist_eq] at h
  rw [hrepr F, hrepr F₀]
  exact h

/-- **Continuity of the `ℓ∞` box mass in the covariance at a nondegenerate `Λ = L Lᵀ`.** For an
invertible `L`, a level `r` whose box frontier is null for `N(0, L Lᵀ)`, and `ε > 0`, there is
`δ > 0` such that every PSD `Σ` entrywise `δ`-close to `L Lᵀ` has
`|N(0,Σ){‖x‖∞ ≤ r} − N(0, L Lᵀ){‖x‖∞ ≤ r}| < ε`. -/
theorem exists_delta_abs_supBoxProb_sub_lt [DecidableEq ι] [Nonempty ι] (L : Matrix ι ι ℝ)
    (hL : IsUnit L.det) (r : ℝ)
    (hnull : ((stdGaussianPi ι).map (L *ᵥ ·)) (frontier {x : ι → ℝ | ∀ i, |x i| ≤ r}) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Matrix ι ι ℝ, S.PosSemidef → (∀ i j, |S i j - (L * Lᵀ) i j| ≤ δ) →
      |supBoxProb S r - ((stdGaussianPi ι).map (L *ᵥ ·)).real {x | ∀ i, |x i| ≤ r}| < ε := by
  set E : Set (ι → ℝ) := {x | ∀ i, |x i| ≤ r} with hEdef
  have hEm : MeasurableSet E := measurableSet_supBox r
  set Λ : Matrix ι ι ℝ := L * Lᵀ with hΛ
  set F₀ : Matrix ι (ι ⊕ ι) ℝ := fromCols L 0 with hF₀
  have hF₀Λ : F₀ * F₀ᵀ = L * Lᵀ := by
    rw [hF₀, transpose_fromCols, fromCols_mul_fromRows]
    simp
  have hmap₀ : (stdGaussianPi (ι ⊕ ι)).map (F₀ *ᵥ ·) = (stdGaussianPi ι).map (L *ᵥ ·) :=
    map_mulVec_stdGaussianPi_eq F₀ L hF₀Λ
  obtain ⟨δ₁, hδ₁, hcont⟩ := exists_delta_abs_map_mulVec_real_sub_lt F₀ hEm
    (by rw [hmap₀]; exact hnull) hε
  -- the quadratic form of `Λ` dominates `(∑|x_i|)²`
  obtain ⟨C, hC, hCx⟩ := exists_sum_abs_sq_le_mul_sumSq Lᵀ (by rwa [det_transpose])
    (fun _ ↦ (1 : ℝ)) fun _ ↦ one_pos
  have hlow : ∀ x : ι → ℝ, (∑ i, |x i|) ^ 2 ≤ C * ∑ i, ∑ j, x i * x j * Λ i j := fun x ↦ by
    rw [hΛ, quadForm_mul_transpose]
    simpa [transpose_apply] using hCx x
  have hQ0 : ∀ x : ι → ℝ, 0 ≤ ∑ i, ∑ j, x i * x j * Λ i j := fun x ↦ by
    rw [hΛ, quadForm_mul_transpose]; positivity
  have hΛsymm : ∀ i j, Λ j i = Λ i j := fun i j ↦ by
    simp only [hΛ, Matrix.mul_apply, transpose_apply]
    exact sum_congr rfl fun k _ ↦ mul_comm _ _
  -- entry bounds
  set a : ℝ := ∑ i, ∑ j, |L i j| + 1 with ha_def
  set b : ℝ := ∑ i, |Λ i i| + 1 with hb_def
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have hLa : ∀ i j, |L i j| ≤ a := fun i j ↦ by
    have h1 : |L i j| ≤ ∑ j', |L i j'| :=
      single_le_sum (f := fun j' ↦ |L i j'|) (fun _ _ ↦ abs_nonneg _) (mem_univ j)
    have h2 : ∑ j', |L i j'| ≤ ∑ i', ∑ j', |L i' j'| :=
      single_le_sum (f := fun i' ↦ ∑ j', |L i' j'|) (fun _ _ ↦ by positivity) (mem_univ i)
    linarith
  have hΛb : ∀ i, |Λ i i| ≤ b := fun i ↦ by
    have h1 : |Λ i i| ≤ ∑ i', |Λ i' i'| :=
      single_le_sum (f := fun i' ↦ |Λ i' i'|) (fun _ _ ↦ abs_nonneg _) (mem_univ i)
    linarith
  set κ : ℝ := min (1 / 2) (min (δ₁ / (2 * a)) (δ₁ ^ 2 / (4 * b))) with hκ_def
  have hκ0 : 0 < κ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hκ1 : κ ≤ 1 / 2 := min_le_left _ _
  have hκa : κ ≤ δ₁ / (2 * a) := (min_le_right _ _).trans (min_le_left _ _)
  have hκb : κ ≤ δ₁ ^ 2 / (4 * b) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min (κ / C) (δ₁ ^ 2 / 4), lt_min (by positivity) (by positivity), fun S hS hSΛ ↦ ?_⟩
  have hδC : ∀ i j, |S i j - Λ i j| ≤ κ / C := fun i j ↦ (hSΛ i j).trans (min_le_left _ _)
  have hδ4 : ∀ i j, |S i j - Λ i j| ≤ δ₁ ^ 2 / 4 := fun i j ↦ (hSΛ i j).trans (min_le_right _ _)
  -- `Σ − (1 − κ)Λ` is PSD
  set P : Matrix ι ι ℝ := S - (1 - κ) • Λ with hPdef
  have hP : P.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg (IsHermitian.ext fun i j ↦ ?_) fun x ↦ ?_
    · have h := hS.1.apply i j
      simp only [star_trivial] at h ⊢
      simp only [hPdef, sub_apply, smul_apply, smul_eq_mul, h, hΛsymm]
    · rw [star_trivial, dotProduct_mulVec_eq_sum]
      have hsplit : ∑ i, ∑ j, x i * x j * P i j =
          ∑ i, ∑ j, x i * x j * S i j - (1 - κ) * ∑ i, ∑ j, x i * x j * Λ i j := by
        simp only [hPdef, sub_apply, smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
        exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
      rw [hsplit]
      have hq := (abs_le.1 (abs_quadForm_sub_le x S Λ hδC)).1
      have hk : (∑ i, |x i|) ^ 2 * (κ / C) ≤ κ * ∑ i, ∑ j, x i * x j * Λ i j := by
        calc (∑ i, |x i|) ^ 2 * (κ / C)
            ≤ (C * ∑ i, ∑ j, x i * x j * Λ i j) * (κ / C) :=
              mul_le_mul_of_nonneg_right (hlow x) (by positivity)
          _ = κ * ∑ i, ∑ j, x i * x j * Λ i j := by field_simp
      linarith
  obtain ⟨Q, hQ⟩ := exists_mul_transpose_eq_of_posSemidef hP
  set c : ℝ := Real.sqrt (1 - κ) with hc_def
  set F : Matrix ι (ι ⊕ ι) ℝ := fromCols (c • L) Q with hFdef
  have hFS : F * Fᵀ = S := by
    rw [hFdef, transpose_fromCols, fromCols_mul_fromRows, hQ, transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hc_def, Real.mul_self_sqrt (by linarith), hPdef]
    abel
  have hG : gaussOfCov S = (stdGaussianPi (ι ⊕ ι)).map (F *ᵥ ·) := gaussOfCov_eq_map hS F hFS
  -- `F` is entrywise close to `F₀`
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcc : c * c = 1 - κ := Real.mul_self_sqrt (by linarith)
  have hc1 : c ≤ 1 := by nlinarith
  have hc2 : 1 - κ ≤ c := by nlinarith
  have hcabs : |c - 1| ≤ κ := abs_le.2 ⟨by linarith, by linarith⟩
  have hclose : ∀ i j, |F i j - F₀ i j| < δ₁ := by
    intro i j
    rcases j with j | j
    · simp only [hFdef, hF₀, fromCols_apply_inl, smul_apply, smul_eq_mul]
      calc |c * L i j - L i j| = |c - 1| * |L i j| := by rw [← abs_mul]; ring_nf
        _ ≤ κ * a := mul_le_mul hcabs (hLa i j) (abs_nonneg _) hκ0.le
        _ ≤ δ₁ / (2 * a) * a := mul_le_mul_of_nonneg_right hκa ha.le
        _ = δ₁ / 2 := by field_simp
        _ < δ₁ := by linarith
    · simp only [hFdef, hF₀, fromCols_apply_inr, zero_apply, sub_zero]
      refine abs_lt_of_sq_lt_sq ?_ hδ₁.le
      have hdiag : (Q * Qᵀ) i i = ∑ k, Q i k ^ 2 := by
        simp only [Matrix.mul_apply, transpose_apply, sq]
      have hle : Q i j ^ 2 ≤ (Q * Qᵀ) i i := by
        rw [hdiag]
        exact single_le_sum (f := fun k ↦ Q i k ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ j)
      rw [hQ] at hle
      have hPii : P i i = (S i i - Λ i i) + κ * Λ i i := by
        simp only [hPdef, sub_apply, smul_apply, smul_eq_mul]; ring
      have h1 := (abs_le.1 (hδ4 i i)).2
      have h2 : κ * Λ i i ≤ δ₁ ^ 2 / 4 := by
        calc κ * Λ i i ≤ κ * b :=
              mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hΛb i)) hκ0.le
          _ ≤ δ₁ ^ 2 / (4 * b) * b := mul_le_mul_of_nonneg_right hκb hb.le
          _ = δ₁ ^ 2 / 4 := by field_simp
      have hd2 : 0 < δ₁ ^ 2 := by positivity
      linarith
  have h := hcont F hclose
  rw [hmap₀] at h
  rw [supBoxProb, hG]
  exact h

end Generic

/-! ## The printed plug-in `Λ̂_T` is PSD -/

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-- The printed plug-in covariance `Λ̂_T = Ā_T⁻¹ Γ̂_T Ā_T⁻ᵀ` (`eq:defn-hat-Lambda`) is positive
semidefinite for every outcome (also on the singular event, where Lean's junk inverse gives `0`). -/
theorem posSemidef_lambdaHat (M : DiscountedMDP State Action) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) : (lambdaHat M η₀ V₀ ω).PosSemidef := by
  have hΓ : (gammaHat M η₀ V₀ ω).PosSemidef := by
    unfold gammaHat
    refine posSemidef_sum _ fun t _ ↦ ?_
    refine PosSemidef.smul ?_ (pluginWeight_nonneg T t)
    simpa using posSemidef_vecMulVec_self_star
      (pluginResidual M (prAverage M η₀ V₀ ω) (ω t))
  have h := hΓ.mul_mul_conjTranspose_same (aBar M ω)⁻¹
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-! ## The plug-in rectangle -/

/-- **Asymptotic coverage of the plug-in `ℓ∞` confidence rectangle (corrected C47(2), asymptotic
only).** For full-support `μ`, `0 < η₀ ≤ 1`, every `V₀`, `Γ_true ≻ 0` and `α ∈ (0,1)`, let
`r̂_T(ω)` be, for every `T` and every outcome `ω`, any `(1 − α)` quantile of `‖X‖∞` for
`X ~ N(0, Λ̂_T(ω))` (`IsSupBoxQuantile`), with the printed plug-in `Λ̂_T = Ā_T⁻¹ Γ̂_T Ā_T⁻ᵀ`
(`lambdaHat`). Then
`P(∀ s, V̄_T(s) − r̂_T/√T ≤ V^π(s) ≤ V̄_T(s) + r̂_T/√T) → 1 − α` as `T → ∞`.
Source: `inference.tex:198–205`, `eq:defn-hat-Lambda` `inference.tex:180–182`. Corrected scaling per
C47(2): half-width `r̂_T/√T` with `r̂_T` the quantile under `Λ̂_T` (the half-width equals `R̂`, the
quantile under `Λ̂_T/T`, by Gaussian scaling; not formalized), not the printed `R̂/√T`. Junk value on the singular event per C47(4); limit
covariance per C43. No rate. -/
theorem tendsto_coverage_rect_plugin [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (rhat : (T : ℕ) → (Fin T → Tuple State Action) → ℝ)
    (hrhat : ∀ (T : ℕ) (ω : Fin T → Tuple State Action),
      IsSupBoxQuantile (lambdaHat M η₀ V₀ ω) α (rhat T ω)) :
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | ∀ s,
          prAverage M η₀ V₀ ω' s - rhat T ω' / Real.sqrt T ≤ M.valueFixedPoint π s ∧
            M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + rhat T ω' / Real.sqrt T}.indicator 1 ω)
      atTop (𝓝 (1 - α)) := by
  classical
  obtain ⟨K₀, -, hb⟩ := exists_confRegion_oracle_bounds M π μ h0 h1 V₀ hμ hΓ
  set L : Matrix State State ℝ := gaussCovFactor (tdA M π μ) (trueGamma M π μ) with hLdef
  have hGL : ∀ r : ℝ, (gaussCov (tdA M π μ) (trueGamma M π μ)).real {x | ∀ s, |x s| ≤ r} =
      ((stdGaussianPi State).map (L *ᵥ ·)).real {x | ∀ s, |x s| ≤ r} := fun r ↦ by
    rw [gaussCov_eq_map_mulVec]
  have hLL : L * Lᵀ = trueLambda M π μ :=
    gaussCovFactor_mul_transpose _ fun s ↦ (hΓ s).le
  have hA : IsUnit (tdA M π μ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ
      (μmin := Finset.univ.inf' Finset.univ_nonempty μ.prob)
      ((Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s) (fun s ↦ Finset.inf'_le _ (mem_univ s)))
  have hLdet : IsUnit L.det := by
    rw [hLdef, gaussCovFactor, det_mul, det_diagonal]
    refine (isUnit_nonsing_inv_det _ hA).mul (isUnit_iff_ne_zero.2 ?_)
    exact Finset.prod_ne_zero_iff.2 fun s _ ↦ (Real.sqrt_pos.2 (hΓ s)).ne'
  have hnull : ∀ r : ℝ,
      ((stdGaussianPi State).map (L *ᵥ ·)) (frontier {x : State → ℝ | ∀ s, |x s| ≤ r}) = 0 :=
    fun r ↦ by
      rw [hLdef, ← gaussCov_eq_map_mulVec]
      exact confCalib_frontier_null M π μ hμ hΓ (convex_supBox r)
  -- events
  let Ev : (T : ℕ) → ℝ → Set (Fin T → Tuple State Action) := fun T r ↦
    {ω' | ∀ s, prAverage M η₀ V₀ ω' s - r / Real.sqrt T ≤ M.valueFixedPoint π s ∧
      M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + r / Real.sqrt T}
  let Eh : (T : ℕ) → Set (Fin T → Tuple State Action) := fun T ↦
    {ω' | ∀ s, prAverage M η₀ V₀ ω' s - rhat T ω' / Real.sqrt T ≤ M.valueFixedPoint π s ∧
      M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + rhat T ω' / Real.sqrt T}
  have hE : ∀ T : ℕ, (∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
      {ω' : Fin T → Tuple State Action | ∀ s,
        prAverage M η₀ V₀ ω' s - rhat T ω' / Real.sqrt T ≤ M.valueFixedPoint π s ∧
          M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + rhat T ω' / Real.sqrt T}.indicator 1 ω) =
      pathProb M π μ T (Eh T) := fun T ↦ rfl
  refine (tendsto_congr hE).2 ?_
  -- fixed-level oracle limits
  have hlimEv : ∀ r : ℝ, Tendsto (fun T : ℕ ↦ pathProb M π μ T (Ev T r)) atTop
      (𝓝 ((gaussCov (tdA M π μ) (trueGamma M π μ)).real {x | ∀ s, |x s| ≤ r})) := by
    intro r
    have hR := tendsto_const_mul_rpow_neg_third_mul_log K₀
    rw [Metric.tendsto_nhds]
    intro η hη
    filter_upwards [eventually_ge_atTop 1, hR.eventually (gt_mem_nhds hη)] with T hT hRT
    rw [Real.dist_eq]
    exact lt_of_le_of_lt ((hb T hT).2.2 r) hRT
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ν : ℝ := min (ε / 4) (min (α / 2) ((1 - α) / 2)) with hν_def
  have hν0 : 0 < ν := lt_min (by positivity) (lt_min (by positivity) (by linarith))
  have hνε : ν ≤ ε / 4 := min_le_left _ _
  have hνα : ν ≤ α / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hν1 : ν ≤ (1 - α) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨rm, -, hrm⟩ := exists_supBox_level_eq M π μ hμ hΓ (α := α + ν) (by linarith)
    (by linarith)
  obtain ⟨rp, -, hrp⟩ := exists_supBox_level_eq M π μ hμ hΓ (α := α - ν) (by linarith)
    (by linarith)
  obtain ⟨δm, hδm, hcm⟩ := exists_delta_abs_supBoxProb_sub_lt L hLdet rm (hnull rm) hν0
  obtain ⟨δp, hδp, hcp⟩ := exists_delta_abs_supBoxProb_sub_lt L hLdet rp (hnull rp) hν0
  let B : (T : ℕ) → Set (Fin T → Tuple State Action) := fun T ↦
    {ω | ∃ s s', min δm δp < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|}
  have hB : Tendsto (fun T : ℕ ↦ pathProb M π μ T (B T)) atTop (𝓝 0) :=
    eq_defn_hat_Lambda_corrected State Action M π μ η₀ V₀ hμ h0 h1 _ (lt_min hδm hδp)
  -- off the bad event, the plug-in level lies in `[rm, rp]`
  have hgood : ∀ (T : ℕ) (ω : Fin T → Tuple State Action), ω ∉ B T →
      rm ≤ rhat T ω ∧ rhat T ω ≤ rp := by
    intro T ω hω
    simp only [B, Set.mem_setOf_eq, not_exists, not_lt] at hω
    rw [← hLL] at hω
    have hm := hcm (lambdaHat M η₀ V₀ ω) (posSemidef_lambdaHat M η₀ V₀ ω)
      fun i j ↦ (hω i j).trans (min_le_left _ _)
    have hp := hcp (lambdaHat M η₀ V₀ ω) (posSemidef_lambdaHat M η₀ V₀ ω)
      fun i j ↦ (hω i j).trans (min_le_right _ _)
    rw [← hGL, hrm] at hm
    rw [← hGL, hrp] at hp
    obtain ⟨hq1, hq2⟩ := hrhat T ω
    exact ⟨hq1 rm (by linarith [(abs_lt.1 hm).2]), hq2 rp (by linarith [(abs_lt.1 hp).1])⟩
  have hsub1 : ∀ T : ℕ, Eh T ⊆ Ev T rp ∪ B T := by
    intro T ω hω
    by_cases hb' : ω ∈ B T
    · exact Or.inr hb'
    · left
      have hle : rhat T ω / Real.sqrt T ≤ rp / Real.sqrt T := by
        gcongr; exact (hgood T ω hb').2
      intro s
      obtain ⟨h1', h2'⟩ := hω s
      exact ⟨by linarith, by linarith⟩
  have hsub2 : ∀ T : ℕ, Ev T rm ⊆ Eh T ∪ B T := by
    intro T ω hω
    by_cases hb' : ω ∈ B T
    · exact Or.inr hb'
    · left
      have hle : rm / Real.sqrt T ≤ rhat T ω / Real.sqrt T := by
        gcongr; exact (hgood T ω hb').1
      intro s
      obtain ⟨h1', h2'⟩ := hω s
      exact ⟨by linarith, by linarith⟩
  filter_upwards [hB.eventually (gt_mem_nhds hν0),
    (hlimEv rm).eventually (Metric.ball_mem_nhds _ hν0),
    (hlimEv rp).eventually (Metric.ball_mem_nhds _ hν0)] with T hBT hmT hpT
  rw [Real.dist_eq, hrm] at hmT
  rw [Real.dist_eq, hrp] at hpT
  have hup : pathProb M π μ T (Eh T) ≤ pathProb M π μ T (Ev T rp) + pathProb M π μ T (B T) :=
    (pathProb_mono M π μ T (hsub1 T)).trans (pathProb_union_le M π μ T _ _)
  have hlo : pathProb M π μ T (Ev T rm) ≤ pathProb M π μ T (Eh T) + pathProb M π μ T (B T) :=
    (pathProb_mono M π μ T (hsub2 T)).trans (pathProb_union_le M π μ T _ _)
  have hB0 : 0 ≤ pathProb M π μ T (B T) := pathProb_nonneg M π μ T _
  have a1 := abs_lt.1 hmT
  have a2 := abs_lt.1 hpT
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-- **Plug-in `ℓ∞` rectangle with the concrete lower quantile (corrected C47(2), asymptotic
only).** Same hypotheses as `tendsto_coverage_rect_plugin`, with
`r̂_T(ω) = supBoxQuantile Λ̂_T(ω) α = inf {r | N(0, Λ̂_T(ω)){‖x‖∞ ≤ r} ≥ 1 − α}`:
`P(∀ s, V̄_T(s) − r̂_T/√T ≤ V^π(s) ≤ V̄_T(s) + r̂_T/√T) → 1 − α`.
Source: `inference.tex:198–205`; corrected scaling per C47(2); C47(4), C43. No rate. -/
theorem tendsto_coverage_rect_plugin_quantile [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    Tendsto (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | ∀ s,
          prAverage M η₀ V₀ ω' s - supBoxQuantile (lambdaHat M η₀ V₀ ω') α / Real.sqrt T ≤
              M.valueFixedPoint π s ∧
            M.valueFixedPoint π s ≤
              prAverage M η₀ V₀ ω' s + supBoxQuantile (lambdaHat M η₀ V₀ ω') α / Real.sqrt T}.indicator
          1 ω)
      atTop (𝓝 (1 - α)) :=
  tendsto_coverage_rect_plugin M π μ h0 h1 V₀ hμ hΓ hα0 hα1
    (fun _ ω ↦ supBoxQuantile (lambdaHat M η₀ V₀ ω) α)
    fun _ _ ↦ isSupBoxQuantile_supBoxQuantile _ hα0 hα1

end StatisticalRL.Ch7Rest.TDInference

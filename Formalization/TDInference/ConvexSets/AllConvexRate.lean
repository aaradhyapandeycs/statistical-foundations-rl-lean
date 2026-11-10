import Formalization.TDInference.ConvexSets.LinearisedRate

/-!
# Partial result toward Theorem 7.11 (not the printed result): the TD estimate over all convex sets at `T^{-2/9}`

Infrastructure for `thm:Berry-Esseen-linear` (`chapters/inference.tex:132–141`; `d_cvx` at
:124–127; `Λ⋆ = A⁻¹ΓA⁻ᵀ` at :104–117, with `Γ := Γ_true`, SOURCE-ISSUES C43).

**This is a partial result, not Theorem 7.11 and not a statement-index entry.** The printed theorem
bounds the convex distance between `√T Δ̄_T` and `N(0, Λ⋆)` by an explicit coefficient times
`T^{-1/3}` (plus `C̃ T^{-1/2}`). Here:
* the rate is `T^{-2/9}`, weaker than the printed `T^{-1/3}`;
* the constant `K` is an instance constant (it may depend on `M, π, μ, η₀, V₀`), not the printed
  coefficient times a universal constant;
* the covariance is the corrected `Γ_true` (SOURCE-ISSUES C43).
The linear-part input is the first (`T^{-1/4}`) pass of the reservoir Lindeberg argument.
The hypothesis `η₀ ≤ 1` is weaker than the printed `η₀ < 1/4`.

Route: write `√T Δ̄_T = linPart + R`. The linear part is within `K₁ T^{-1/4}` of the Gaussian target
over all convex sets (`abs_linLaw_convex_sub_gaussCov_le_quarter`, M6.3). The remainder has
`‖R_s‖_{L²} ≤ K_E T^{-1/3}` for each coordinate (`weightedL2_scaledError_sub_linPart_le`), so by
Chebyshev `P(‖R‖_∞ > δ) ≤ S K_E² T^{-2/3} / δ²`. Sandwiching `C` between its inner parallel set
`{y | closedBall y δ ⊆ C}` and `cthickening δ C` (both convex) costs the Gaussian mass of the
`δ`-shell of `C`, which is `≤ c δ` (`tdGaussCov_convexShell_le_diagMin`, M1). With
`δ = T^{-2/9}` all three terms are `O(T^{-2/9})`.

Main export: `abs_lawProb_convex_sub_gaussCov_le_twoNinths`.
-/

open Finset Matrix MeasureTheory Metric
open scoped BigOperators

namespace StatisticalRL.Probability

/-! ## Generic perturbation lemmas (finite weights) -/

section Perturb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The inner parallel set `{y | closedBall y δ ⊆ C}` of a convex set is convex. -/
theorem convex_setOf_closedBall_subset {C : Set E} (hC : Convex ℝ C) (δ : ℝ) :
    Convex ℝ {y | closedBall y δ ⊆ C} := by
  intro x hx y hy a b ha hb hab z hz
  set d := z - (a • x + b • y) with hd
  have hdn : ‖d‖ ≤ δ := by
    rw [hd, ← dist_eq_norm]; exact mem_closedBall.1 hz
  have hxd : x + d ∈ C := hx (mem_closedBall.2 (by rw [dist_self_add_left]; exact hdn))
  have hyd : y + d ∈ C := hy (mem_closedBall.2 (by rw [dist_self_add_left]; exact hdn))
  have he : a • (x + d) + b • (y + d) = z := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul, hd]
    abel
  rw [← he]
  exact hC hxd hyd ha hb hab

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι]

/-- **Transfer of a convex-set bound across a small perturbation** (any finite weights `w ≥ 0`).
If `Y` is within `a` of `ν` on every convex set, the `δ`-shell of the convex `C` has `ν`-mass
`≤ b`, and `‖X − Y‖ > δ` has weight `≤ q`, then `|P(X ∈ C) − ν(C)| ≤ a + b + q`. -/
theorem abs_sum_indicator_sub_le_of_perturb {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (X Y : Ω → ι → ℝ) (ν : Measure (ι → ℝ)) [IsFiniteMeasure ν] {δ a b q : ℝ}
    (hY : ∀ K : Set (ι → ℝ), Convex ℝ K →
      |∑ ω, w ω * K.indicator (fun _ ↦ (1 : ℝ)) (Y ω) - ν.real K| ≤ a)
    {C : Set (ι → ℝ)} (hC : Convex ℝ C)
    (hsh : ν.real (cthickening δ C ∩ cthickening δ (interior C)ᶜ) ≤ b)
    (hq : ∑ ω, w ω * (if δ < ‖X ω - Y ω‖ then (1 : ℝ) else 0) ≤ q) :
    |∑ ω, w ω * C.indicator (fun _ ↦ (1 : ℝ)) (X ω) - ν.real C| ≤ a + b + q := by
  set bad : Ω → ℝ := fun ω ↦ if δ < ‖X ω - Y ω‖ then (1 : ℝ) else 0 with hbad
  set I : Set (ι → ℝ) := {y | closedBall y δ ⊆ C}
  set shell := cthickening δ C ∩ cthickening δ (interior C)ᶜ
  have hind : ∀ (K : Set (ι → ℝ)) (x : ι → ℝ),
      K.indicator (fun _ ↦ (1 : ℝ)) x ∈ Set.Icc (0 : ℝ) 1 := fun K x ↦ by
    by_cases h : x ∈ K
    · rw [Set.indicator_of_mem h]; exact ⟨zero_le_one, le_rfl⟩
    · rw [Set.indicator_of_notMem h]; exact ⟨le_rfl, zero_le_one⟩
  have hbad0 : ∀ ω, 0 ≤ bad ω := fun ω ↦ by simp only [hbad]; split_ifs <;> norm_num
  -- upper bound, pointwise
  have hup : ∀ ω, C.indicator (fun _ ↦ (1 : ℝ)) (X ω) ≤
      (cthickening δ C).indicator (fun _ ↦ (1 : ℝ)) (Y ω) + bad ω := by
    intro ω
    by_cases hb : δ < ‖X ω - Y ω‖
    · have : bad ω = 1 := by simp only [hbad, if_pos hb]
      rw [this]
      linarith [(hind C (X ω)).2, (hind (cthickening δ C) (Y ω)).1]
    · have : bad ω = 0 := by simp only [hbad, if_neg hb]
      rw [this, add_zero]
      by_cases hX : X ω ∈ C
      · have hYm : Y ω ∈ cthickening δ C :=
          mem_cthickening_of_dist_le (Y ω) (X ω) δ C hX
            (by rw [dist_eq_norm, norm_sub_rev]; exact not_lt.1 hb)
        rw [Set.indicator_of_mem hX, Set.indicator_of_mem hYm]
      · rw [Set.indicator_of_notMem hX]; exact (hind _ _).1
  -- lower bound, pointwise
  have hlo : ∀ ω, I.indicator (fun _ ↦ (1 : ℝ)) (Y ω) ≤
      C.indicator (fun _ ↦ (1 : ℝ)) (X ω) + bad ω := by
    intro ω
    by_cases hb : δ < ‖X ω - Y ω‖
    · have : bad ω = 1 := by simp only [hbad, if_pos hb]
      rw [this]
      linarith [(hind I (Y ω)).2, (hind C (X ω)).1]
    · have : bad ω = 0 := by simp only [hbad, if_neg hb]
      rw [this, add_zero]
      by_cases hY' : Y ω ∈ I
      · have hX : X ω ∈ C := hY' (mem_closedBall.2 (by rw [dist_eq_norm]; exact not_lt.1 hb))
        rw [Set.indicator_of_mem hX, Set.indicator_of_mem hY']
      · rw [Set.indicator_of_notMem hY']; exact (hind _ _).1
  have hsumup : ∑ ω, w ω * C.indicator (fun _ ↦ (1 : ℝ)) (X ω) ≤
      ∑ ω, w ω * (cthickening δ C).indicator (fun _ ↦ (1 : ℝ)) (Y ω) + q := by
    calc ∑ ω, w ω * C.indicator (fun _ ↦ (1 : ℝ)) (X ω)
        ≤ ∑ ω, (w ω * (cthickening δ C).indicator (fun _ ↦ (1 : ℝ)) (Y ω) + w ω * bad ω) :=
          sum_le_sum fun ω _ ↦ by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hup ω) (hw ω)
      _ = ∑ ω, w ω * (cthickening δ C).indicator (fun _ ↦ (1 : ℝ)) (Y ω) + ∑ ω, w ω * bad ω :=
          sum_add_distrib
      _ ≤ _ := by linarith [hq]
  have hsumlo : ∑ ω, w ω * I.indicator (fun _ ↦ (1 : ℝ)) (Y ω) ≤
      ∑ ω, w ω * C.indicator (fun _ ↦ (1 : ℝ)) (X ω) + q := by
    calc ∑ ω, w ω * I.indicator (fun _ ↦ (1 : ℝ)) (Y ω)
        ≤ ∑ ω, (w ω * C.indicator (fun _ ↦ (1 : ℝ)) (X ω) + w ω * bad ω) :=
          sum_le_sum fun ω _ ↦ by rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hlo ω) (hw ω)
      _ = ∑ ω, w ω * C.indicator (fun _ ↦ (1 : ℝ)) (X ω) + ∑ ω, w ω * bad ω := sum_add_distrib
      _ ≤ _ := by linarith [hq]
  have h1 := abs_le.1 (hY _ (hC.cthickening δ))
  have h2 := abs_le.1 (hY _ (convex_setOf_closedBall_subset hC δ))
  -- the Gaussian side
  have hν1 : ν.real (cthickening δ C) ≤ ν.real C + ν.real shell := by
    refine (measureReal_mono fun x hx ↦ ?_).trans (measureReal_union_le C shell)
    by_cases hxC : x ∈ C
    · exact Or.inl hxC
    · exact Or.inr ⟨hx, self_subset_cthickening _ fun h ↦ hxC (interior_subset h)⟩
  have hν2 : ν.real C ≤ ν.real I + ν.real shell := by
    refine (measureReal_mono fun x hx ↦ ?_).trans (measureReal_union_le I shell)
    by_cases hxI : x ∈ I
    · exact Or.inl hxI
    · exact Or.inr
        (ConvexSandwichShell.diff_innerParallel_subset_convexShell C δ ⟨hx, hxI⟩)
  rw [abs_le]
  constructor <;> linarith

/-- **Chebyshev for the sup norm** (finite weights). For `δ > 0`,
`P(‖Z‖_∞ > δ) ≤ ∑_s E[Z_s²] / δ²`. -/
theorem sum_mul_ite_lt_norm_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (Z : Ω → ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∑ ω, w ω * (if δ < ‖Z ω‖ then (1 : ℝ) else 0) ≤
      ∑ s, (∑ ω, w ω * Z ω s ^ 2) / δ ^ 2 := by
  have hpt : ∀ ω, (if δ < ‖Z ω‖ then (1 : ℝ) else 0) ≤ ∑ s, Z ω s ^ 2 / δ ^ 2 := by
    intro ω
    split_ifs with h
    · by_contra hc
      have hall : ∀ s, |Z ω s| ≤ δ := by
        intro s
        by_contra hs
        have hs' : δ < |Z ω s| := not_le.1 hs
        have hsq : δ ^ 2 < Z ω s ^ 2 := by
          rw [← sq_abs (Z ω s)]; exact pow_lt_pow_left₀ hs' hδ.le (by norm_num)
        have h1 : 1 < Z ω s ^ 2 / δ ^ 2 := (one_lt_div (by positivity)).2 hsq
        have h2 : Z ω s ^ 2 / δ ^ 2 ≤ ∑ s, Z ω s ^ 2 / δ ^ 2 :=
          single_le_sum (f := fun s ↦ Z ω s ^ 2 / δ ^ 2) (fun s _ ↦ by positivity) (mem_univ s)
        exact hc (by linarith)
      have : ‖Z ω‖ ≤ δ :=
        (pi_norm_le_iff_of_nonneg hδ.le).2 fun s ↦ by rw [Real.norm_eq_abs]; exact hall s
      linarith
    · exact sum_nonneg fun s _ ↦ by positivity
  calc ∑ ω, w ω * (if δ < ‖Z ω‖ then (1 : ℝ) else 0)
      ≤ ∑ ω, w ω * ∑ s, Z ω s ^ 2 / δ ^ 2 :=
        sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hpt ω) (hw ω)
    _ = ∑ s, (∑ ω, w ω * Z ω s ^ 2) / δ ^ 2 := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun s _ ↦ ?_
        rw [sum_div]
        exact sum_congr rfl fun ω _ ↦ by ring

end Perturb

end StatisticalRL.Probability

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-! ## Rate arithmetic -/

/-- `(T^{-1/3})² / (T^{-2/9})² = T^{-2/9}` for `T > 0`. -/
theorem rpow_third_sq_div_rpow_twoNinths_sq {T : ℝ} (hT : 0 < T) :
    (T ^ (-(1 / 3 : ℝ))) ^ 2 / (T ^ (-(2 / 9 : ℝ))) ^ 2 = T ^ (-(2 / 9 : ℝ)) := by
  rw [← div_pow, ← Real.rpow_sub hT, ← Real.rpow_natCast, ← Real.rpow_mul hT.le]
  norm_num

omit [Fintype State] [DecidableEq State] in
/-- `T^{-1/4} ≤ T^{-2/9}` for `T ≥ 1`. -/
theorem rpow_neg_quarter_le_twoNinths {T : ℕ} (hT : 1 ≤ T) :
    (T : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (T : ℝ) ^ (-(2 / 9 : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hT) (by norm_num)

/-! ## The remainder tail -/

/-- **Chebyshev for the linearisation remainder.** For `δ > 0`, `T ≥ 1`:
`P(‖√TΔ̄_T − linPart‖_∞ > δ) ≤ S (K_E T^{-1/3})² / δ²`. -/
theorem sum_pathWeight_remainder_tail_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) {μmin : ℝ} (hμmin0 : 0 < μmin)
    (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T) {δ : ℝ} (hδ : 0 < δ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        (if δ < ‖scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω‖ then (1 : ℝ) else 0) ≤
      Fintype.card State *
        ((linRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 / δ ^ 2) := by
  have hw := pathWeight_nonneg M π μ (T := T)
  refine (sum_mul_ite_lt_norm_le hw
    (fun ω ↦ scaledError M π η₀ V₀ ω - linPart M π μ η₀ ω) hδ).trans ?_
  rw [← nsmul_eq_mul, ← Finset.card_univ, ← sum_const]
  refine sum_le_sum fun s _ ↦ div_le_div_of_nonneg_right ?_ (by positivity)
  have hL := weightedL2_scaledError_sub_linPart_le M π μ h0 h1 V₀ hμmin0 hμmin hT s
  have hsq := sq_weightedL2 hw
    (fun ω : Fin T → Tuple State Action ↦ scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s)
  exact (le_of_eq hsq.symm).trans (pow_le_pow_left₀ (weightedL2_nonneg _ _) hL 2)

/-! ## Main export -/

/-- **Partial result toward Theorem 7.11 (not the printed result): all convex sets at the weaker rate `T^{-2/9}`** (infrastructure,
**partial, not the printed result**, no statement-index entry). For full-support `μ`, `0 < η₀ ≤ 1`,
every initial value `V₀` and `Γ_true ≻ 0`, there is an instance constant `K > 0` (depending on
`M, π, μ, η₀, V₀`) such that for every `T ≥ 1` and every convex `C ⊆ ℝ^S` (measurable or not;
`gaussCov.real` is the outer measure)
`|P(√T Δ̄_T ∈ C) − N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)(C)| ≤ K T^{-2/9}`.

Differences from `thm:Berry-Esseen-linear` (`chapters/inference.tex:132–141`): the rate is
`T^{-2/9}` instead of `T^{-1/3}`; the constant is an instance constant instead of the printed
coefficient; the covariance uses `Γ_true` (SOURCE-ISSUES C43). -/
theorem abs_lawProb_convex_sub_gaussCov_le_twoNinths [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
        K * (T : ℝ) ^ (-(2 / 9 : ℝ)) := by
  obtain ⟨K₁, hK₁, hlin⟩ := abs_linLaw_convex_sub_gaussCov_le_quarter M π μ h0 h1 hμ hΓ
  set μmin := diagMin μ.prob
  have hμmin0 : 0 < μmin := (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s
  have hμmin : ∀ s, μmin ≤ μ.prob s := fun s ↦ Finset.inf'_le _ (mem_univ s)
  set Csh := 4 * (Fintype.card State : ℝ) ^ 2 * (2 / Real.sqrt (diagMin (trueGamma M π μ))) /
    Real.sqrt (2 * Real.pi) with hCsh
  set KE := linRemainderConst M π V₀ μmin η₀
  have hCsh0 : 0 ≤ Csh := by rw [hCsh]; positivity
  refine ⟨K₁ + Csh + Fintype.card State * KE ^ 2, by positivity, fun T hT C hC ↦ ?_⟩
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  set δ := (T : ℝ) ^ (-(2 / 9 : ℝ)) with hδ_def
  have hδ : 0 < δ := Real.rpow_pos_of_pos hT0 _
  have hw := pathWeight_nonneg M π μ (T := T)
  have hsh := tdGaussCov_convexShell_le_diagMin M π μ hμmin0 hμmin hΓ hC hδ.le
  have hq := sum_pathWeight_remainder_tail_le M π μ h0 h1 V₀ hμmin0 hμmin hT hδ
  have hmain := abs_sum_indicator_sub_le_of_perturb hw
    (fun ω ↦ scaledError M π η₀ V₀ ω) (fun ω ↦ linPart M π μ η₀ ω)
    (gaussCov (tdA M π μ) (trueGamma M π μ)) (fun K hK ↦ hlin T hT K hK) hC hsh hq
  have e1 : 4 * (Fintype.card State : ℝ) ^ 2 * (2 / Real.sqrt (diagMin (trueGamma M π μ))) * δ /
      Real.sqrt (2 * Real.pi) = Csh * δ := by rw [hCsh]; ring
  have e2 : (Fintype.card State : ℝ) * ((KE * (T : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 / δ ^ 2) =
      Fintype.card State * KE ^ 2 * δ := by
    rw [mul_pow, mul_div_assoc, hδ_def, rpow_third_sq_div_rpow_twoNinths_sq hT0]
    ring
  rw [e1, e2] at hmain
  refine hmain.trans ?_
  have hq4 := rpow_neg_quarter_le_twoNinths hT
  have : K₁ * (T : ℝ) ^ (-(1 / 4 : ℝ)) ≤ K₁ * δ := mul_le_mul_of_nonneg_left hq4 hK₁.le
  rw [add_mul, add_mul]
  linarith

end StatisticalRL.Ch7Rest.TDInference

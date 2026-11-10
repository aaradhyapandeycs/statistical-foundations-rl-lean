import Formalization.Ch7Rest.TDInferenceConvexThird711
import Formalization.Ch7Rest.TDInferenceHalfSpace711
import Formalization.Ch7Rest.TDInferenceOperator711

/-!
# Oracle-covariance confidence regions: fixed shape, corrected ellipsoid, corrected rectangle

Source: `chapters/inference.tex:187–213` (rule `eq:convex.Cdelta` :189–196, rectangles :198–205,
ellipsoids :207–213) and `docs/SOURCE-ISSUES.md` C47. These are **corrected and oracle-restricted
forms, not the printed formulas**, and a **partial** result for `eq:convex.Cdelta`.

Let `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (`trueLambda`, the covariance of the Gaussian target `gaussCov`).
`Λ` is the **oracle** covariance: it is unknown in practice (the printed rule uses the plug-in
`Λ̂_T`, whose finite-`T` rate remains open). Under full-support `μ`, `0 < η₀ ≤ 1`, every `V₀`
and `Γ_true ≻ 0`, there is one **instance constant** `K₀ > 0` (it may depend on
`M, π, μ, η₀, V₀`) such that for all `T ≥ 1`, with rate `T^{-1/3} log(2T)` (weaker than the
printed `T^{-1/3}` by the factor `log(2T)`):

1. fixed shape (C47 proposed correction): for every convex `K ⊆ ℝ^S` fixed before the data,
   `|P(V^π ∈ V̄_T + T^{-1/2} K) − N(0,Λ)(K)| ≤ K₀ T^{-1/3} log(2T)`;
2. ellipsoid, corrected per C47(3) (threshold `q`, not `q²`): for every `q`,
   `|P(T (V^π − V̄_T)ᵀ Λ⁻¹ (V^π − V̄_T) ≤ q) − N(0,Λ){x | xᵀΛ⁻¹x ≤ q}| ≤ K₀ T^{-1/3} log(2T)`;
3. rectangle, corrected per C47(2) (half-width `r/√T`, `√T` applied once): for every `r`,
   `|P(∀ s, V̄_T(s) − r/√T ≤ V^π(s) ≤ V̄_T(s) + r/√T) − N(0,Λ){‖x‖∞ ≤ r}| ≤ K₀ T^{-1/3} log(2T)`.

All three follow from `abs_lawProb_convex_sub_gaussCov_le_third_log` (convex sets, `T^{-1/3}log(2T)`)
with one constant: (1) via `−K` and the symmetry `N(0,Λ)(−K) = N(0,Λ)(K)` (`gaussCov_real_neg`);
(2) via `Λ⁻¹ = Aᵀ diag(Γ_true)⁻¹ A` (`trueLambda_inv_eq`), so the ellipsoid is a convex sublevel set
of `∑_r (Ax)_r² / Γ_r`; (3) the sup-norm box is convex.
Not done here (the plug-in rate is in `TDInferencePlugin{Interval,Ellipsoid,Rect}Rate711.lean`): data-selected convex sets (C47(1)), and continuity
in `q` / `r` of the Gaussian side (only the sets are fixed; existence of an exact `1 − α` threshold is not
proved here). The same corollaries at rate `T^{-1/3}` without `log(2T)` follow in the same way from
`abs_lawProb_convex_sub_gaussCov_le_third_sharp` (`TDInferenceConvexSharp711.lean`) but are not re-derived here.
-/

open MeasureTheory ProbabilityTheory Finset Matrix
open scoped BigOperators Pointwise

namespace StatisticalRL.Ch7Rest.TDInference

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-! ## Symmetry of the centred Gaussian `gaussCov` -/

omit [DecidableEq State] in
/-- The standard Gaussian on `State → ℝ` is invariant under negation. -/
theorem stdGaussPi_map_neg :
    (Measure.pi fun _ : State ↦ gaussianReal 0 1).map (fun z ↦ -z) =
      Measure.pi fun _ : State ↦ gaussianReal 0 1 := by
  have h : (fun z : State → ℝ ↦ -z) = fun z i ↦ (fun x : ℝ ↦ -x) (z i) := by
    funext z i; rfl
  rw [h, Measure.pi_map_pi (fun _ ↦ measurable_neg.aemeasurable)]
  simp_rw [gaussianReal_map_neg, neg_zero]

theorem gaussMap_neg (A : Matrix State State ℝ) (Γ : State → ℝ) (z : State → ℝ) :
    gaussMap A Γ (-z) = -gaussMap A Γ z := by
  unfold gaussMap
  rw [← Matrix.mulVec_neg]
  congr 1
  funext s
  simp only [Pi.neg_apply, mul_neg]

/-- `gaussCov A Γ = N(0, A⁻¹ diag(Γ) A⁻ᵀ)` is symmetric: its image under `x ↦ −x` is itself. -/
theorem gaussCov_map_neg (A : Matrix State State ℝ) (Γ : State → ℝ) :
    (gaussCov A Γ).map (fun x ↦ -x) = gaussCov A Γ := by
  unfold gaussCov
  rw [Measure.map_map measurable_neg (measurable_gaussMap A Γ)]
  have : (fun x : State → ℝ ↦ -x) ∘ gaussMap A Γ = gaussMap A Γ ∘ (fun z ↦ -z) := by
    funext z; simp only [Function.comp_apply, gaussMap_neg]
  rw [this, ← Measure.map_map (measurable_gaussMap A Γ) measurable_neg, stdGaussPi_map_neg]

/-- `N(0, A⁻¹ diag(Γ) A⁻ᵀ)(−K) = N(0, A⁻¹ diag(Γ) A⁻ᵀ)(K)` for every set `K` (outer measure for
non-measurable `K`). -/
theorem gaussCov_real_neg (A : Matrix State State ℝ) (Γ : State → ℝ) (K : Set (State → ℝ)) :
    (gaussCov A Γ).real (-K) = (gaussCov A Γ).real K := by
  conv_rhs => rw [← gaussCov_map_neg A Γ]
  have e := MeasurableEquiv.map_apply (μ := gaussCov A Γ) (MeasurableEquiv.neg (State → ℝ)) K
  simp only [measureReal_def]
  rw [show (fun x : State → ℝ ↦ -x) = ⇑(MeasurableEquiv.neg (State → ℝ)) from rfl, e]
  rfl

/-! ## Fixed-shape rule `V̄_T + T^{-1/2} K` -/

omit [Fintype State] [DecidableEq State] in
theorem mem_vadd_inv_sqrt_smul_iff {T : ℕ} (hT : 1 ≤ T) (V v : State → ℝ)
    (K : Set (State → ℝ)) :
    V ∈ v +ᵥ (Real.sqrt T)⁻¹ • K ↔ -(Real.sqrt T • (v - V)) ∈ K := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.2 hT').ne'
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hs),
    inv_inv, vadd_eq_add]
  have e : Real.sqrt T • (-v + V) = -(Real.sqrt T • (v - V)) := by
    rw [smul_add, smul_sub, smul_neg]; abel
  rw [e]

/-- The fixed-shape coverage probability `P(V^π ∈ V̄_T + T^{-1/2} K)` is `P(√TΔ̄_T ∈ −K)`. -/
theorem sum_pathWeight_fixedShape_eq_lawProb (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T) (K : Set (State → ℝ)) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action |
          M.valueFixedPoint π ∈ prAverage M η₀ V₀ ω' +ᵥ (Real.sqrt T)⁻¹ • K}.indicator 1 ω =
      lawProb M π μ η₀ V₀ T (-K) := by
  classical
  unfold lawProb
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  congr 1
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, Set.mem_neg,
    mem_vadd_inv_sqrt_smul_iff hT, scaledError]

/-- **Fixed-shape oracle confidence regions (C47 proposed correction).** One instance constant
`K₀ > 0` such that for all `T ≥ 1` and every convex `K` fixed before the data,
`|P(V^π ∈ V̄_T + T^{-1/2} K) − N(0, Λ)(K)| ≤ K₀ T^{-1/3} log(2T)`, `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`
(oracle covariance). -/
theorem exists_fixedShape_coverage_le [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) (hμ : ∀ s, 0 < μ.prob s)
    (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ T : ℕ, 1 ≤ T → ∀ K : Set (State → ℝ), Convex ℝ K →
      |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action |
            M.valueFixedPoint π ∈ prAverage M η₀ V₀ ω' +ᵥ (Real.sqrt T)⁻¹ • K}.indicator 1 ω -
        (gaussCov (tdA M π μ) (trueGamma M π μ)).real K| ≤
        K₀ * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T)) := by
  obtain ⟨K₀, hK₀, hb⟩ := abs_lawProb_convex_sub_gaussCov_le_third_log M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K₀, hK₀, fun T hT K hK ↦ ?_⟩
  rw [sum_pathWeight_fixedShape_eq_lawProb M π μ η₀ V₀ hT K, ← gaussCov_real_neg _ _ K]
  exact hb T hT (-K) hK.neg

/-! ## Corrected rectangle (C47(2)) -/

omit [Fintype State] [DecidableEq State] in
/-- The sup-norm box `{x | ∀ s, |x s| ≤ r}` is convex. -/
theorem convex_supBox (r : ℝ) : Convex ℝ {x : State → ℝ | ∀ s, |x s| ≤ r} := by
  intro x hx y hy a b ha hb hab
  rw [Set.mem_setOf_eq] at hx hy ⊢
  intro s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc |a * x s + b * y s| ≤ |a * x s| + |b * y s| := abs_add_le _ _
    _ = a * |x s| + b * |y s| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * r + b * r := by gcongr; exacts [hx s, hy s]
    _ = r := by rw [← add_mul, hab, one_mul]

theorem interval_iff_abs_mul_le {t : ℝ} (ht : 0 < t) (v V r : ℝ) :
    (v - r / t ≤ V ∧ V ≤ v + r / t) ↔ |t * (v - V)| ≤ r := by
  have e : r / t * t = r := div_mul_cancel₀ r ht.ne'
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 ht.le,
      mul_le_mul_of_nonneg_left h2 ht.le]
  · rintro ⟨h1, h2⟩
    have hq : r / t * t = r := e
    constructor
    · by_contra h; push_neg at h
      have := mul_lt_mul_of_pos_right h ht
      nlinarith
    · by_contra h; push_neg at h
      have := mul_lt_mul_of_pos_right h ht
      nlinarith

/-- The corrected rectangle coverage `P(∀ s, |V̄_T(s) − V^π(s)| ≤ r/√T)` is `P(‖√TΔ̄_T‖∞ ≤ r)`. -/
theorem sum_pathWeight_supRect_eq_lawProb (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T) (r : ℝ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | ∀ s,
          prAverage M η₀ V₀ ω' s - r / Real.sqrt T ≤ M.valueFixedPoint π s ∧
            M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + r / Real.sqrt T}.indicator 1 ω =
      lawProb M π μ η₀ V₀ T {x | ∀ s, |x s| ≤ r} := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT'
  classical
  unfold lawProb
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  congr 1
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, interval_iff_abs_mul_le hs,
    scaledError, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

/-! ## Corrected ellipsoid (C47(3)) -/

/-- `(Aᵀ diag(Γ_true)⁻¹ A) Λ = 1` for `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`, under full-support `μ` and
`Γ_true ≻ 0`. -/
theorem trueLambda_left_inv [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    (tdA M π μ)ᵀ * diagonal (fun s ↦ (trueGamma M π μ s)⁻¹) * tdA M π μ * trueLambda M π μ = 1 := by
  set μmin := Finset.univ.inf' Finset.univ_nonempty μ.prob
  have hμmin0 : 0 < μmin := (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s
  have hμmin : ∀ s, μmin ≤ μ.prob s := fun s ↦ Finset.inf'_le _ (mem_univ s)
  have hA : IsUnit (tdA M π μ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)
  set A := tdA M π μ
  set Γ := trueGamma M π μ
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have h2 : diagonal (fun s ↦ (Γ s)⁻¹) * diagonal Γ = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext s
    exact inv_mul_cancel₀ (hΓ s).ne'
  have h3 : Aᵀ * A⁻¹ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul A hA, transpose_one]
  calc Aᵀ * diagonal (fun s ↦ (Γ s)⁻¹) * A * trueLambda M π μ
      = Aᵀ * (diagonal (fun s ↦ (Γ s)⁻¹) * ((A * A⁻¹) * (diagonal Γ * A⁻¹ᵀ))) := by
        simp only [trueLambda, Matrix.mul_assoc]; rfl
    _ = 1 := by
        rw [h1, Matrix.one_mul, ← Matrix.mul_assoc (diagonal fun s ↦ (Γ s)⁻¹), h2, Matrix.one_mul, h3]

/-- `Λ⁻¹ = Aᵀ diag(Γ_true)⁻¹ A` for `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`, under full-support `μ` and
`Γ_true ≻ 0`. -/
theorem trueLambda_inv_eq [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    (trueLambda M π μ)⁻¹ =
      (tdA M π μ)ᵀ * diagonal (fun s ↦ (trueGamma M π μ s)⁻¹) * tdA M π μ :=
  Matrix.inv_eq_left_inv (trueLambda_left_inv M π μ hμ hΓ)

/-- `Λ` is invertible: `Λ⁻¹ Λ = 1` (so the Lean `Matrix.inv` in the ellipsoid is the genuine
inverse, not the junk value `0`). -/
theorem trueLambda_inv_mul [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    (trueLambda M π μ)⁻¹ * trueLambda M π μ = 1 := by
  rw [trueLambda_inv_eq M π μ hμ hΓ]
  exact trueLambda_left_inv M π μ hμ hΓ

/-- `xᵀΛ⁻¹x = ∑_r (Ax)_r² / Γ_true(r)`. -/
theorem quadForm_trueLambda_inv [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) (x : State → ℝ) :
    ∑ s, ∑ s', x s * x s' * (trueLambda M π μ)⁻¹ s s' =
      ∑ r, (∑ s, x s * tdA M π μ r s) ^ 2 * (trueGamma M π μ r)⁻¹ := by
  rw [trueLambda_inv_eq M π μ hμ hΓ]
  have h := quadForm_mul_diagonal_mul_transpose (tdA M π μ)ᵀ
    (fun s ↦ (trueGamma M π μ s)⁻¹) x
  rw [Matrix.transpose_transpose] at h
  rw [h]
  rfl

omit [DecidableEq State] in
/-- Sublevel sets of `x ↦ ∑_r (∑_s x_s B_{rs})² c_r` with `c ≥ 0` are convex. -/
theorem convex_sumSq_le (B : Matrix State State ℝ) (c : State → ℝ) (hc : ∀ r, 0 ≤ c r)
    (q : ℝ) : Convex ℝ {x : State → ℝ | ∑ r, (∑ s, x s * B r s) ^ 2 * c r ≤ q} := by
  intro x hx y hy a b ha hb hab
  rw [Set.mem_setOf_eq] at hx hy ⊢
  obtain rfl : b = 1 - a := by linarith
  have key : ∀ r, (∑ s, (a • x + (1 - a) • y) s * B r s) ^ 2 * c r ≤
      a * ((∑ s, x s * B r s) ^ 2 * c r) + (1 - a) * ((∑ s, y s * B r s) ^ 2 * c r) := by
    intro r
    have hlin : ∑ s, (a • x + (1 - a) • y) s * B r s =
        a * ∑ s, x s * B r s + (1 - a) * ∑ s, y s * B r s := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hlin]
    have hid : a * ((∑ s, x s * B r s) ^ 2 * c r) + (1 - a) * ((∑ s, y s * B r s) ^ 2 * c r) -
        (a * ∑ s, x s * B r s + (1 - a) * ∑ s, y s * B r s) ^ 2 * c r =
        a * (1 - a) * ((∑ s, x s * B r s - ∑ s, y s * B r s) ^ 2 * c r) := by ring
    have hnn : 0 ≤ a * (1 - a) * ((∑ s, x s * B r s - ∑ s, y s * B r s) ^ 2 * c r) :=
      mul_nonneg (mul_nonneg ha hb) (mul_nonneg (sq_nonneg _) (hc r))
    linarith
  calc ∑ r, (∑ s, (a • x + (1 - a) • y) s * B r s) ^ 2 * c r
      ≤ ∑ r, (a * ((∑ s, x s * B r s) ^ 2 * c r) + (1 - a) * ((∑ s, y s * B r s) ^ 2 * c r)) :=
        Finset.sum_le_sum fun r _ ↦ key r
    _ = a * ∑ r, (∑ s, x s * B r s) ^ 2 * c r + (1 - a) * ∑ r, (∑ s, y s * B r s) ^ 2 * c r := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * q + (1 - a) * q := by gcongr
    _ = q := by ring

/-- The ellipsoid `{x | xᵀΛ⁻¹x ≤ q}` is convex (`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`). -/
theorem convex_trueLambda_ellipsoid [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) (q : ℝ) :
    Convex ℝ {x : State → ℝ | ∑ s, ∑ s', x s * x s' * (trueLambda M π μ)⁻¹ s s' ≤ q} := by
  have e : {x : State → ℝ | ∑ s, ∑ s', x s * x s' * (trueLambda M π μ)⁻¹ s s' ≤ q} =
      {x : State → ℝ | ∑ r, (∑ s, x s * tdA M π μ r s) ^ 2 * (trueGamma M π μ r)⁻¹ ≤ q} := by
    ext x
    simp only [Set.mem_setOf_eq, quadForm_trueLambda_inv M π μ hμ hΓ x]
  rw [e]
  exact convex_sumSq_le _ _ (fun r ↦ (inv_pos.2 (hΓ r)).le) q

/-- The corrected ellipsoid coverage `P(T (V^π − V̄_T)ᵀ L (V^π − V̄_T) ≤ q)` is
`P((√TΔ̄_T)ᵀ L (√TΔ̄_T) ≤ q)`, for any matrix `L`. -/
theorem sum_pathWeight_ellipsoid_eq_lawProb (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) (L : Matrix State State ℝ) (q : ℝ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
          (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
            (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') * L s s' ≤ q}.indicator 1 ω =
      lawProb M π μ η₀ V₀ T {x | ∑ s, ∑ s', x s * x s' * L s s' ≤ q} := by
  have hT2 : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (Nat.cast_nonneg _)
  classical
  unfold lawProb
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  congr 1
  have e : (T : ℝ) * ∑ s, ∑ s', (M.valueFixedPoint π s - prAverage M η₀ V₀ ω s) *
      (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω s') * L s s' =
      ∑ s, ∑ s', scaledError M π η₀ V₀ ω s * scaledError M π η₀ V₀ ω s' * L s s' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ ↦ ?_
    simp only [scaledError, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination (-((M.valueFixedPoint π s - prAverage M η₀ V₀ ω s) *
      (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω s') * L s s')) * hT2
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, e]

/-! ## Combined export -/

/-- **Oracle-covariance confidence regions at `T^{-1/3} log(2T)` (corrected forms, partial for
`eq:convex.Cdelta`).** For full-support `μ`, `0 < η₀ ≤ 1`, every `V₀` and `Γ_true ≻ 0`, with
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (`trueLambda`, the oracle covariance, unknown in practice), there is one
instance constant `K₀ > 0` such that for all `T ≥ 1`:
1. every convex `K` (fixed before the data):
   `|P(V^π ∈ V̄_T + T^{-1/2} K) − N(0,Λ)(K)| ≤ K₀ T^{-1/3} log(2T)`;
2. every `q` (ellipsoid corrected per C47(3), threshold `q`):
   `|P(T (V^π − V̄_T)ᵀ Λ⁻¹ (V^π − V̄_T) ≤ q) − N(0,Λ){xᵀΛ⁻¹x ≤ q}| ≤ K₀ T^{-1/3} log(2T)`;
3. every `r` (rectangle corrected per C47(2), half-width `r/√T`):
   `|P(∀ s, V̄_T(s) − r/√T ≤ V^π(s) ≤ V̄_T(s) + r/√T) − N(0,Λ){‖x‖∞ ≤ r}| ≤ K₀ T^{-1/3} log(2T)`.
These are not the printed formulas (C47(2)/(3)); the rate is weaker than the printed `T^{-1/3}` by
`log(2T)`; the plug-in-covariance versions with rate `T^{-1/3}` are in `TDInferencePlugin{Interval,Ellipsoid,Rect}Rate711.lean`. -/
theorem exists_confRegion_oracle_bounds [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀)
    (h1 : η₀ ≤ 1) (V₀ : State → ℝ) (hμ : ∀ s, 0 < μ.prob s)
    (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ T : ℕ, 1 ≤ T →
      (∀ K : Set (State → ℝ), Convex ℝ K →
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action |
              M.valueFixedPoint π ∈ prAverage M η₀ V₀ ω' +ᵥ (Real.sqrt T)⁻¹ • K}.indicator 1 ω -
          (gaussCov (tdA M π μ) (trueGamma M π μ)).real K| ≤
          K₀ * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T))) ∧
      (∀ q : ℝ,
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
              (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
                (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                  (trueLambda M π μ)⁻¹ s s' ≤ q}.indicator 1 ω -
          (gaussCov (tdA M π μ) (trueGamma M π μ)).real
            {x | ∑ s, ∑ s', x s * x s' * (trueLambda M π μ)⁻¹ s s' ≤ q}| ≤
          K₀ * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T))) ∧
      (∀ r : ℝ,
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∀ s,
              prAverage M η₀ V₀ ω' s - r / Real.sqrt T ≤ M.valueFixedPoint π s ∧
                M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + r / Real.sqrt T}.indicator 1 ω -
          (gaussCov (tdA M π μ) (trueGamma M π μ)).real {x | ∀ s, |x s| ≤ r}| ≤
          K₀ * ((T : ℝ) ^ (-(1 / 3 : ℝ)) * Real.log (2 * T))) := by
  obtain ⟨K₀, hK₀, hb⟩ := abs_lawProb_convex_sub_gaussCov_le_third_log M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K₀, hK₀, fun T hT ↦ ⟨fun K hK ↦ ?_, fun q ↦ ?_, fun r ↦ ?_⟩⟩
  · rw [sum_pathWeight_fixedShape_eq_lawProb M π μ η₀ V₀ hT K, ← gaussCov_real_neg _ _ K]
    exact hb T hT (-K) hK.neg
  · rw [sum_pathWeight_ellipsoid_eq_lawProb M π μ η₀ V₀ T]
    exact hb T hT _ (convex_trueLambda_ellipsoid M π μ hμ hΓ q)
  · rw [sum_pathWeight_supRect_eq_lawProb M π μ η₀ V₀ hT r]
    exact hb T hT _ (convex_supBox r)

end StatisticalRL.Ch7Rest.TDInference

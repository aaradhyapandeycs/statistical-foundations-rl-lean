import Formalization.TDInference.HalfSpace

/-!
# Oracle-covariance confidence intervals from the half-space Theorem 7.11 (plan item B)

Source: `chapters/inference.tex:187–196` (the rule `eq:convex.Cdelta` :189–195, display :191–193,
and the claim that "such sets serve as approximate confidence regions" :196), the rectangle prose
:198–205, and SOURCE-ISSUES C47(1)–(2). The covariance is `Λ = A⁻¹Γ_trueA⁻ᵀ`, the population target
of the printed plug-in `Λ̂_T` (:180–182); C43 concerns the printed `Λ⋆` (:106–117) of Theorem 7.11.

All results are corollaries of the corrected half-space bound
`abs_lawProb_halfSpace_sub_gaussCov_le` (`TDInference/HalfSpace.lean`), with one constant `K`
taken once from it and uniform in the direction `u`, the level `z` and `T ≥ 1`.

Let `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (the **oracle** covariance, unknown in practice) and
`q(u) = uᵀΛu`, `Φ(z) = N(0,1)(-∞, z]` (written `(gaussianReal 0 1).real (Set.Iic z)`).

* B1, one-sided (`abs_coverage_oneSided_sub_le`): for all `z ∈ ℝ` and `u ≠ 0`,
  `|P(uᵀV^π ≥ uᵀV̄_T − z√(q(u)/T)) − Φ(z)| ≤ K T^{-1/3}`.
* B2, two-sided (`abs_coverage_twoSided_sub_le`): for `z ≥ 0` and `u ≠ 0`,
  `|P(|uᵀ(V̄_T − V^π)| ≤ z√(q(u)/T)) − (2Φ(z) − 1)| ≤ 2K T^{-1/3}`.
* B3, Bonferroni box (`coverage_rect_bonferroni_ge`): for `z ≥ 0`,
  `P(∀ s, |V̄_T(s) − V^π(s)| ≤ z√(Λ_ss/T)) ≥ 1 − 2S(1 − Φ(z)) − 2SK T^{-1/3}`.

`u` and `z` are fixed before the data (the set's shape does not depend on the sample), so
C47(1) (data-selected sets) does not apply. Not addressed: the plug-in `Λ̂_T` (C47(4)), arbitrary
convex sets, the printed `ℓ∞`-quantile rectangle (C47(2)) and the ellipsoid (C47(3)).
The combined export `exists_coverage_oracle_bounds` gives all three with one `K`.
-/

open MeasureTheory ProbabilityTheory Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Probability.Stein StatisticalRL.Analysis

/-! ## Real-number reformulations of the events -/

/-- `a − z√(r/T) ≤ b ⇔ √T (a − b) ≤ z√r` for `T > 0`. -/
theorem sub_mul_sqrt_div_le_iff (a b z r T : ℝ) (hT : 0 < T) :
    a - z * Real.sqrt (r / T) ≤ b ↔ Real.sqrt T * (a - b) ≤ z * Real.sqrt r := by
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  rw [Real.sqrt_div' r hT.le, ← mul_div_assoc, mul_comm (Real.sqrt T), ← le_div_iff₀ hsT]
  constructor <;> intro h <;> linarith

/-- `|d| ≤ z√(r/T) ⇔ |√T d| ≤ z√r` for `T > 0`. -/
theorem abs_le_mul_sqrt_div_iff (d z r T : ℝ) (hT : 0 < T) :
    |d| ≤ z * Real.sqrt (r / T) ↔ |Real.sqrt T * d| ≤ z * Real.sqrt r := by
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  rw [Real.sqrt_div' r hT.le, ← mul_div_assoc, le_div_iff₀ hsT, abs_mul, abs_of_pos hsT,
    mul_comm]

/-- For `c ≥ 0`, `1{|w| ≤ c} = 1{w ≤ c} + 1{−w ≤ c} − 1`. -/
theorem ite_abs_le_eq {w c : ℝ} (hc : 0 ≤ c) :
    (if |w| ≤ c then (1 : ℝ) else 0) =
      (if w ≤ c then (1 : ℝ) else 0) + (if -w ≤ c then (1 : ℝ) else 0) - 1 := by
  have h : |w| ≤ c ↔ w ≤ c ∧ -w ≤ c := by
    rw [abs_le]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases h1 : w ≤ c <;> by_cases h2 : -w ≤ c
  · simp [h, h1, h2]
  · simp [h, h1, h2]
  · simp [h, h1, h2]
  · exfalso; linarith

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-! ## Gaussian side and positivity of the quadratic form -/

/-- For `Γ ≥ 0` and `q = uᵀ(A⁻¹ diag(Γ) A⁻ᵀ)u > 0`,
`N(0, A⁻¹ diag(Γ) A⁻ᵀ){x | uᵀx ≤ z√q} = Φ(z)`. -/
theorem gaussCov_real_halfSpace_mul_sqrt (A : Matrix State State ℝ) (Γ : State → ℝ)
    (hΓ : ∀ s, 0 ≤ Γ s) (u : State → ℝ)
    (hq : 0 < ∑ s, ∑ s', u s * u s' * (A⁻¹ * diagonal Γ * A⁻¹ᵀ) s s') (z : ℝ) :
    (gaussCov A Γ).real {x | ∑ s, u s * x s ≤
        z * Real.sqrt (∑ s, ∑ s', u s * u s' * (A⁻¹ * diagonal Γ * A⁻¹ᵀ) s s')} =
      (gaussianReal 0 1).real (Set.Iic z) := by
  have hQ := quadForm_mul_diagonal_mul_transpose A⁻¹ Γ u
  rw [hQ] at hq ⊢
  rw [gaussCov_real_halfSpace A Γ hΓ u, gaussianReal_real_Iic_eq_stdCDF (by simpa using hq),
    gaussianReal_real_Iic]
  congr 1
  simp only [NNReal.coe_mk]
  rw [mul_div_assoc, div_self (Real.sqrt_pos.2 hq).ne', mul_one]

/-- `uᵀΛu > 0` for `u ≠ 0`, with `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`, under full-support `μ` and
`Γ_true ≻ 0`. -/
theorem quadForm_oracle_pos [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) {u : State → ℝ} (hu : u ≠ 0) :
    0 < ∑ s, ∑ s', u s * u s' *
      ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s' := by
  set μmin := Finset.univ.inf' Finset.univ_nonempty μ.prob
  have hμmin0 : 0 < μmin := (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s
  have hμmin : ∀ s, μmin ≤ μ.prob s := fun s ↦ Finset.inf'_le _ (mem_univ s)
  set g := Finset.univ.inf' Finset.univ_nonempty (trueGamma M π μ)
  have hg0 : 0 < g := (Finset.lt_inf'_iff _).2 fun s _ ↦ hΓ s
  have hg : ∀ s, g ≤ trueGamma M π μ s := fun s ↦ Finset.inf'_le _ (mem_univ s)
  have hA : IsUnit (tdA M π μ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)
  have hb := mul_sq_sum_abs_le_quadForm (tdA M π μ) hA (trueGamma M π μ) hg0.le hg u
  rw [← quadForm_mul_diagonal_mul_transpose] at hb
  obtain ⟨s, hs⟩ := Function.ne_iff.1 hu
  have hsum : 0 < ∑ s, |u s| :=
    lt_of_lt_of_le (abs_pos.2 hs)
      (single_le_sum (f := fun s ↦ |u s|) (fun _ _ ↦ abs_nonneg _) (mem_univ s))
  have hlhs : 0 < g * (∑ s, |u s|) ^ 2 := by positivity
  set D := (Fintype.card State : ℝ) * (∑ r, ∑ s, |tdA M π μ r s|) ^ 2 + 1
  have hD : 0 < D := by positivity
  by_contra hneg
  push_neg at hneg
  have : D * (∑ s, ∑ s', u s * u s' *
      ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s') ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hD.le hneg
  linarith

/-! ## The half-space bound in `Φ` form -/

/-- **Half-space bound at the pivot.** One `K` such that, for all `T ≥ 1`, `u ≠ 0` and `z ∈ ℝ`,
`|P(uᵀ√TΔ̄_T ≤ z√(uᵀΛu)) − Φ(z)| ≤ K T^{-1/3}`. -/
theorem exists_abs_lawProb_halfSpace_pivot_sub_le [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ,
      |lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ z * Real.sqrt (∑ s, ∑ s', u s * u s' *
          ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s')} -
        (gaussianReal 0 1).real (Set.Iic z)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := abs_lawProb_halfSpace_sub_gaussCov_le M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K, hK, fun T hT u hu z ↦ ?_⟩
  have h := hb T hT u (z * Real.sqrt (∑ s, ∑ s', u s * u s' *
    ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s'))
  rwa [gaussCov_real_halfSpace_mul_sqrt _ _ (fun s ↦ (hΓ s).le) u
    (quadForm_oracle_pos M π μ hμ hΓ hu) z] at h

/-- `lawProb` of a symmetric slab is `P(H(u)) + P(H(−u)) − 1` for `c ≥ 0`. -/
theorem lawProb_slab_eq (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ) (T : ℕ) (u : State → ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    lawProb M π μ η₀ V₀ T {x | |∑ s, u s * x s| ≤ c} =
      lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ c} +
        lawProb M π μ η₀ V₀ T {x | ∑ s, (-u) s * x s ≤ c} - 1 := by
  rw [← lawProb_univ M π μ η₀ V₀ T]
  simp only [lawProb, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun ω _ ↦ ?_
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Set.mem_univ, if_true, Pi.neg_apply,
    neg_mul, sum_neg_distrib]
  rw [ite_abs_le_eq hc]
  ring

/-- **Two-sided half-space bound at the pivot.** For `z ≥ 0` and `u ≠ 0`,
`|P(|uᵀ√TΔ̄_T| ≤ z√(uᵀΛu)) − (2Φ(z) − 1)| ≤ 2K T^{-1/3}` with the `K` of the one-sided bound. -/
theorem abs_lawProb_slab_pivot_sub_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {K : ℝ} (T : ℕ)
    (hK : ∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ,
      |lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ z * Real.sqrt (∑ s, ∑ s', u s * u s' *
          ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s')} -
        (gaussianReal 0 1).real (Set.Iic z)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ)))
    {u : State → ℝ} (hu : u ≠ 0) {z : ℝ} (hz : 0 ≤ z) :
    |lawProb M π μ η₀ V₀ T {x | |∑ s, u s * x s| ≤ z * Real.sqrt (∑ s, ∑ s', u s * u s' *
          ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s')} -
        (2 * (gaussianReal 0 1).real (Set.Iic z) - 1)| ≤ 2 * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  set Λ := (tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ
  have hneg : ∑ s, ∑ s', (-u) s * (-u) s' * Λ s s' = ∑ s, ∑ s', u s * u s' * Λ s s' := by
    simp only [Pi.neg_apply, neg_mul_neg]
  have hu' : -u ≠ 0 := neg_ne_zero.2 hu
  have h1 := hK u hu z
  have h2 := hK (-u) hu' z
  rw [hneg] at h2
  rw [lawProb_slab_eq M π μ η₀ V₀ T u (mul_nonneg hz (Real.sqrt_nonneg _))]
  calc |lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ z * Real.sqrt (∑ s, ∑ s', u s * u s' * Λ s s')} +
          lawProb M π μ η₀ V₀ T {x | ∑ s, (-u) s * x s ≤
            z * Real.sqrt (∑ s, ∑ s', u s * u s' * Λ s s')} - 1 -
          (2 * (gaussianReal 0 1).real (Set.Iic z) - 1)|
      = |(lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤
            z * Real.sqrt (∑ s, ∑ s', u s * u s' * Λ s s')} - (gaussianReal 0 1).real (Set.Iic z)) +
          (lawProb M π μ η₀ V₀ T {x | ∑ s, (-u) s * x s ≤
            z * Real.sqrt (∑ s, ∑ s', u s * u s' * Λ s s')} -
            (gaussianReal 0 1).real (Set.Iic z))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ)) + K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := add_le_add h1 h2
    _ = 2 * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by ring

/-! ## Data-side events -/

/-- `uᵀ√TΔ̄_T = √T (uᵀV̄_T − uᵀV^π)`. -/
theorem sum_mul_scaledError (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ} (ω : Fin T → Tuple State Action) (u : State → ℝ) :
    ∑ s, u s * scaledError M π η₀ V₀ ω s =
      Real.sqrt T * (∑ s, u s * prAverage M η₀ V₀ ω s - ∑ s, u s * M.valueFixedPoint π s) := by
  rw [← sum_sub_distrib, Finset.mul_sum]
  refine sum_congr rfl fun s _ ↦ ?_
  simp only [scaledError, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- The one-sided coverage probability is a half-space probability of `√TΔ̄_T`. -/
theorem sum_pathWeight_oneSided_eq_lawProb (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T) (u : State → ℝ) (z r : ℝ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | ∑ s, u s * prAverage M η₀ V₀ ω' s -
          z * Real.sqrt (r / T) ≤ ∑ s, u s * M.valueFixedPoint π s}.indicator 1 ω =
      lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ z * Real.sqrt r} := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  refine sum_congr rfl fun ω _ ↦ ?_
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, sum_mul_scaledError,
    sub_mul_sqrt_div_le_iff _ _ z r _ hT']

/-- The two-sided coverage probability is a slab probability of `√TΔ̄_T`. -/
theorem sum_pathWeight_twoSided_eq_lawProb (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T) (u : State → ℝ) (z r : ℝ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action |
          |∑ s, u s * (prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s)| ≤
            z * Real.sqrt (r / T)}.indicator 1 ω =
      lawProb M π μ η₀ V₀ T {x | |∑ s, u s * x s| ≤ z * Real.sqrt r} := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  refine sum_congr rfl fun ω _ ↦ ?_
  have he : ∑ s, u s * (prAverage M η₀ V₀ ω s - M.valueFixedPoint π s) =
      ∑ s, u s * prAverage M η₀ V₀ ω s - ∑ s, u s * M.valueFixedPoint π s := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun s _ ↦ by ring
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, sum_mul_scaledError, he,
    abs_le_mul_sqrt_div_iff _ z r _ hT']

/-! ## B1 and B2 -/

/-- **B1, one-sided oracle interval.** For every instance with full-support `μ`, `Γ_true ≻ 0`,
`0 < η₀ ≤ 1` and any `V₀`, there is `K > 0` such that for all `T ≥ 1`, `u ≠ 0` and `z ∈ ℝ`,
`|P(uᵀV̄_T − z√(uᵀΛu/T) ≤ uᵀV^π) − Φ(z)| ≤ K T^{-1/3}`, `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`. -/
theorem abs_coverage_oneSided_sub_le [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ,
      |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | ∑ s, u s * prAverage M η₀ V₀ ω' s -
            z * Real.sqrt ((∑ s, ∑ s', u s * u s' *
              ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s') / T) ≤
            ∑ s, u s * M.valueFixedPoint π s}.indicator 1 ω) -
        (gaussianReal 0 1).real (Set.Iic z)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := exists_abs_lawProb_halfSpace_pivot_sub_le M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K, hK, fun T hT u hu z ↦ ?_⟩
  rw [sum_pathWeight_oneSided_eq_lawProb M π μ η₀ V₀ hT]
  exact hb T hT u hu z

/-- **B2, two-sided oracle interval.** Same hypotheses; for all `T ≥ 1`, `u ≠ 0` and `z ≥ 0`,
`|P(|uᵀ(V̄_T − V^π)| ≤ z√(uᵀΛu/T)) − (2Φ(z) − 1)| ≤ 2K T^{-1/3}`. -/
theorem abs_coverage_twoSided_sub_le [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ, 0 ≤ z →
      |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action |
            |∑ s, u s * (prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s)| ≤
              z * Real.sqrt ((∑ s, ∑ s', u s * u s' *
                ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s') / T)}.indicator
            1 ω) -
        (2 * (gaussianReal 0 1).real (Set.Iic z) - 1)| ≤ 2 * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := exists_abs_lawProb_halfSpace_pivot_sub_le M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K, hK, fun T hT u hu z hz ↦ ?_⟩
  rw [sum_pathWeight_twoSided_eq_lawProb M π μ η₀ V₀ hT]
  exact abs_lawProb_slab_pivot_sub_le M π μ η₀ V₀ T (hb T hT) hu hz

/-! ## B3: Bonferroni box -/

/-- **Union bound for `lawProb`.** `P(∀ s, √TΔ̄_T ∈ C_s) ≥ 1 − ∑_s (1 − P(√TΔ̄_T ∈ C_s))`. -/
theorem one_sub_sum_le_lawProb_forall (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) (C : State → Set (State → ℝ)) :
    1 - ∑ s, (1 - lawProb M π μ η₀ V₀ T (C s)) ≤
      lawProb M π μ η₀ V₀ T {x | ∀ s, x ∈ C s} := by
  set w := fun ω : Fin T → Tuple State Action ↦ pathWeight M π μ ω
  set i := fun (s : State) (ω : Fin T → Tuple State Action) ↦
    (C s).indicator (fun _ ↦ (1 : ℝ)) (scaledError M π η₀ V₀ ω)
  have hw : ∑ ω, w ω = 1 := sum_pathWeight M π μ T
  have hpt : ∀ ω, 1 - ∑ s, (1 - i s ω) ≤
      {x : State → ℝ | ∀ s, x ∈ C s}.indicator (fun _ ↦ (1 : ℝ)) (scaledError M π η₀ V₀ ω) := by
    intro ω
    by_cases h : ∀ s, scaledError M π η₀ V₀ ω ∈ C s
    · have h1 : ∀ s, i s ω = 1 := fun s ↦ by simp [i, h s]
      simp only [h1, sub_self, sum_const_zero, sub_zero]
      simp [h]
    · push_neg at h
      obtain ⟨s0, hs0⟩ := h
      have hle : ∀ s, 0 ≤ 1 - i s ω := fun s ↦ by
        classical
        simp only [i]; rw [Set.indicator_apply]; split_ifs <;> norm_num
      have hsum : 1 ≤ ∑ s, (1 - i s ω) := by
        have := single_le_sum (f := fun s ↦ 1 - i s ω) (fun s _ ↦ hle s) (mem_univ s0)
        simpa [i, Set.indicator_apply, hs0] using this
      have h0 : 0 ≤ {x : State → ℝ | ∀ s, x ∈ C s}.indicator (fun _ ↦ (1 : ℝ))
          (scaledError M π η₀ V₀ ω) := Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
      linarith
  calc 1 - ∑ s, (1 - lawProb M π μ η₀ V₀ T (C s))
      = ∑ ω, w ω - ∑ s, ∑ ω, (w ω - w ω * i s ω) := by
        rw [hw]
        congr 1
        refine sum_congr rfl fun s _ ↦ ?_
        rw [sum_sub_distrib, hw]
        rfl
    _ = ∑ ω, w ω - ∑ ω, ∑ s, (w ω - w ω * i s ω) := by rw [Finset.sum_comm]
    _ = ∑ ω, w ω * (1 - ∑ s, (1 - i s ω)) := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun ω _ ↦ ?_
        rw [mul_sub, mul_one, Finset.mul_sum]
        congr 1
        exact sum_congr rfl fun s _ ↦ by ring
    _ ≤ ∑ ω, w ω * {x : State → ℝ | ∀ s, x ∈ C s}.indicator (fun _ ↦ (1 : ℝ))
          (scaledError M π η₀ V₀ ω) :=
        sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hpt ω) (pathWeight_nonneg M π μ ω)
    _ = lawProb M π μ η₀ V₀ T {x | ∀ s, x ∈ C s} := rfl

/-- The coordinate direction `e_s`: `e_sᵀx = x_s`. -/
theorem sum_single_mul (s : State) (x : State → ℝ) :
    ∑ s', (Pi.single s (1 : ℝ) : State → ℝ) s' * x s' = x s := by
  simp [Pi.single_apply]

/-- `e_sᵀ Λ e_s = Λ_ss`. -/
theorem quadForm_single (s : State) (Λ : Matrix State State ℝ) :
    ∑ a, ∑ b, (Pi.single s (1 : ℝ) : State → ℝ) a * (Pi.single s (1 : ℝ) : State → ℝ) b *
      Λ a b = Λ s s := by
  simp [Pi.single_apply]

omit [Fintype State] in
theorem single_one_ne_zero (s : State) : (Pi.single s (1 : ℝ) : State → ℝ) ≠ 0 := by
  intro h
  have := congrFun h s
  simp at this

/-- **Bonferroni box, `lawProb` form.** With the `K` of the one-sided pivot bound, for `z ≥ 0`,
`P(∀ s, |√TΔ̄_T(s)| ≤ z√Λ_ss) ≥ 1 − 2S(1 − Φ(z)) − 2SK T^{-1/3}`. -/
theorem lawProb_rect_ge (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ) {K : ℝ} (T : ℕ)
    (hK : ∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ,
      |lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ z * Real.sqrt (∑ s, ∑ s', u s * u s' *
          ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s')} -
        (gaussianReal 0 1).real (Set.Iic z)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ)))
    {z : ℝ} (hz : 0 ≤ z) :
    1 - 2 * (Fintype.card State : ℝ) * (1 - (gaussianReal 0 1).real (Set.Iic z)) -
        2 * (Fintype.card State : ℝ) * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) ≤
      lawProb M π μ η₀ V₀ T {x | ∀ s, |x s| ≤ z * Real.sqrt
        (((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s)} := by
  set Λ := (tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ
  set Φz := (gaussianReal 0 1).real (Set.Iic z)
  set r := K * (T : ℝ) ^ (-(1 / 3 : ℝ))
  have hcoord : ∀ s, 1 - lawProb M π μ η₀ V₀ T {x | |x s| ≤ z * Real.sqrt (Λ s s)} ≤
      2 * (1 - Φz) + 2 * r := by
    intro s
    have h := abs_lawProb_slab_pivot_sub_le M π μ η₀ V₀ T hK (single_one_ne_zero s) hz
    simp only [sum_single_mul, quadForm_single] at h
    have := (abs_le.1 h).1
    linarith
  have hsum := sum_le_sum fun s (_ : s ∈ univ) ↦ hcoord s
  rw [sum_const, card_univ, nsmul_eq_mul] at hsum
  have hu := one_sub_sum_le_lawProb_forall M π μ η₀ V₀ T
    (fun s ↦ {x : State → ℝ | |x s| ≤ z * Real.sqrt (Λ s s)})
  simp only [Set.mem_setOf_eq] at hu
  have : 2 * (Fintype.card State : ℝ) * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) =
      2 * (Fintype.card State : ℝ) * r := by simp only [r]; ring
  rw [this]
  nlinarith [hsum, hu]

/-- The box coverage probability is a `lawProb` of `√TΔ̄_T`. -/
theorem sum_pathWeight_rect_eq_lawProb (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (hT : 1 ≤ T) (z : ℝ) (r : State → ℝ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        {ω' : Fin T → Tuple State Action | ∀ s,
          |prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s| ≤
            z * Real.sqrt (r s / T)}.indicator 1 ω =
      lawProb M π μ η₀ V₀ T {x | ∀ s, |x s| ≤ z * Real.sqrt (r s)} := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  refine sum_congr rfl fun ω _ ↦ ?_
  have he : ∀ s, scaledError M π η₀ V₀ ω s =
      Real.sqrt T * (prAverage M η₀ V₀ ω s - M.valueFixedPoint π s) := fun s ↦ by
    simp only [scaledError, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, he,
    abs_le_mul_sqrt_div_iff _ z _ _ hT']

/-! ## Combined export: B1, B2, B3 with one constant -/

/-- **Oracle-covariance coverage, B1–B3 with one `K`.** For every instance with full-support
`μ`, `Γ_true ≻ 0`, `0 < η₀ ≤ 1` and every `V₀`, there is `K > 0` such that for every `T ≥ 1`:
(B1) for all `u ≠ 0`, `z ∈ ℝ`, `|P(uᵀV̄_T − z√(uᵀΛu/T) ≤ uᵀV^π) − Φ(z)| ≤ K T^{-1/3}`;
(B2) for all `u ≠ 0`, `z ≥ 0`, `|P(|uᵀ(V̄_T − V^π)| ≤ z√(uᵀΛu/T)) − (2Φ(z) − 1)| ≤ 2K T^{-1/3}`;
(B3) for all `z ≥ 0`, `P(∀ s, |V̄_T(s) − V^π(s)| ≤ z√(Λ_ss/T)) ≥ 1 − 2S(1−Φ(z)) − 2SK T^{-1/3}`;
here `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` and `Φ(z) = N(0,1)(-∞, z]`. -/
theorem exists_coverage_oracle_bounds [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T →
      (∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ,
        |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∑ s, u s * prAverage M η₀ V₀ ω' s -
              z * Real.sqrt ((∑ s, ∑ s', u s * u s' *
                ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s') / T) ≤
              ∑ s, u s * M.valueFixedPoint π s}.indicator 1 ω) -
          (gaussianReal 0 1).real (Set.Iic z)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ, 0 ≤ z →
        |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action |
              |∑ s, u s * (prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s)| ≤
                z * Real.sqrt ((∑ s, ∑ s', u s * u s' *
                  ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s') /
                    T)}.indicator 1 ω) -
          (2 * (gaussianReal 0 1).real (Set.Iic z) - 1)| ≤
            2 * K * (T : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (∀ z : ℝ, 0 ≤ z →
        1 - 2 * (Fintype.card State : ℝ) * (1 - (gaussianReal 0 1).real (Set.Iic z)) -
            2 * (Fintype.card State : ℝ) * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) ≤
          ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∀ s,
              |prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s| ≤
                z * Real.sqrt ((((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) *
                  (tdA M π μ)⁻¹ᵀ) s s) / T)}.indicator 1 ω) := by
  obtain ⟨K, hK, hb⟩ := exists_abs_lawProb_halfSpace_pivot_sub_le M π μ h0 h1 V₀ hμ hΓ
  refine ⟨K, hK, fun T hT ↦ ⟨fun u hu z ↦ ?_, fun u hu z hz ↦ ?_, fun z hz ↦ ?_⟩⟩
  · rw [sum_pathWeight_oneSided_eq_lawProb M π μ η₀ V₀ hT]
    exact hb T hT u hu z
  · rw [sum_pathWeight_twoSided_eq_lawProb M π μ η₀ V₀ hT]
    exact abs_lawProb_slab_pivot_sub_le M π μ η₀ V₀ T (hb T hT) hu hz
  · rw [sum_pathWeight_rect_eq_lawProb M π μ η₀ V₀ hT]
    exact lawProb_rect_ge M π μ η₀ V₀ T (hb T hT) hz

/-- **B3, Bonferroni box (oracle covariance).** For all `T ≥ 1` and `z ≥ 0`,
`P(∀ s, |V̄_T(s) − V^π(s)| ≤ z√(Λ_ss/T)) ≥ 1 − 2S(1 − Φ(z)) − 2SK T^{-1/3}`. -/
theorem coverage_rect_bonferroni_ge [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ z : ℝ, 0 ≤ z →
      1 - 2 * (Fintype.card State : ℝ) * (1 - (gaussianReal 0 1).real (Set.Iic z)) -
          2 * (Fintype.card State : ℝ) * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) ≤
        ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | ∀ s,
            |prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s| ≤
              z * Real.sqrt ((((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) *
                (tdA M π μ)⁻¹ᵀ) s s) / T)}.indicator 1 ω := by
  obtain ⟨K, hK, hb⟩ := exists_coverage_oracle_bounds M π μ h0 h1 V₀ hμ hΓ
  exact ⟨K, hK, fun T hT ↦ (hb T hT).2.2⟩

end StatisticalRL.Ch7Rest.TDInference

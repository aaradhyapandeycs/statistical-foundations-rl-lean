import Formalization.Ch7Rest.TDInferenceQuadForm711
import Formalization.Ch7Rest.TDInferenceLeaveOneOutBound711
import Formalization.Probability.ChenShaoNonlinear
import Formalization.Probability.StdGaussianPi
import Mathlib.Algebra.Order.Chebyshev

/-!
# Theorem 7.11, corrected covariance, closed half-spaces (M9)

Source: `chapters/inference.tex:132–141` (`thm:Berry-Esseen-linear`), objects :47–127,
covariance corrected to `Γ_true` (SOURCE-ISSUES C43). This module assembles the half-space
Berry–Esseen bound at the printed rate `T^{-1/3}`:

for `0 < η₀ ≤ 1`, full-support `μ`, `Γ_true ≻ 0` and every `V₀` there is `K` such that for all
`T ≥ 1`, `u : State → ℝ` and `b : ℝ`,
`|P(uᵀ√TΔ̄_T ≤ b) − N(0, A⁻¹Γ_trueA⁻ᵀ){x | uᵀx ≤ b}| ≤ K T^{-1/3}`.

Ingredients:
* Gaussian side: `stdGaussianPi_map_sum_mul` (the law of `∑ cᵢZᵢ` is `N(0, ∑ cᵢ²)`, by
  characteristic functions), hence `gaussCov_real_halfSpace`: the Gaussian half-space mass is
  `Φ(b/√q)` with `q = uᵀΛu`.
* Lower bound `q ≥ c (∑|u|)²` (`mul_sq_sum_abs_le_quadForm`), `c > 0` instance-dependent.
* Data side: the Chen–Shao bound `chenShao_nonlinear_of_var` applied to
  `W = uᵀlinPart = ∑ᵢ uᵀlinSummandᵢ(ωᵢ)` and `Δ = uᵀ(√TΔ̄_T − linPart)` (transient included),
  with the M5/M8 estimates `weightedL2_proj_scaledError_sub_linPart_le`, `sum_looChenShao_le`,
  `abs_proj_linSummand_le`.
* Variance step: `abs_stdCDF_div_sub_le` with `abs_quadForm_linCov_sub_le`; for small `T`
  (where `uᵀΛ_Tu ≥ uᵀΛu/2` is not yet guaranteed) the trivial bound `|·| ≤ 1`.
-/

open MeasureTheory ProbabilityTheory Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Probability.Stein StatisticalRL.Analysis

/-! ## Gaussian side -/

section Gaussian

variable {ι : Type*} [Fintype ι]

/-- **Gaussian projection.** For i.i.d. standard Gaussian coordinates `Z`, the law of `∑ᵢ cᵢZᵢ`
is `N(0, ∑ᵢ cᵢ²)` (any real `c`, zero allowed). -/
theorem stdGaussianPi_map_sum_mul (c : ι → ℝ) :
    (stdGaussianPi ι).map (fun z ↦ ∑ i, c i * z i) =
      gaussianReal 0 ⟨∑ i, c i ^ 2, sum_nonneg fun _ _ ↦ sq_nonneg _⟩ := by
  have hm : Measurable (fun z : ι → ℝ ↦ ∑ i, c i * z i) := by fun_prop
  haveI : IsProbabilityMeasure ((stdGaussianPi ι).map (fun z ↦ ∑ i, c i * z i)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  rw [charFun_apply_real, integral_map hm.aemeasurable (by fun_prop), charFun_gaussianReal]
  have h1 : ∀ z : ι → ℝ, Complex.exp (↑t * ↑(∑ i, c i * z i) * Complex.I) =
      ∏ i, Complex.exp (↑(t * c i) * ↑(z i) * Complex.I) := by
    intro z
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  simp_rw [h1]
  rw [show stdGaussianPi ι = Measure.pi (fun _ : ι ↦ gaussianReal 0 1) from rfl,
    integral_fintype_prod_eq_prod (fun i (x : ℝ) ↦ Complex.exp (↑(t * c i) * ↑x * Complex.I))]
  have h2 : ∀ i, ∫ x, Complex.exp (↑(t * c i) * ↑x * Complex.I) ∂(gaussianReal 0 1) =
      Complex.exp (-(↑(t * c i) : ℂ) ^ 2 / 2) := by
    intro i
    rw [← charFun_apply_real, charFun_gaussianReal]
    congr 1
    push_cast
    ring
  simp_rw [h2]
  rw [← Complex.exp_sum]
  congr 1
  simp only [NNReal.coe_mk]
  push_cast
  rw [Finset.sum_mul, Finset.sum_div, mul_zero, zero_mul, zero_sub, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

end Gaussian

variable {State Action : Type} [Fintype State] [Fintype Action]

/-- **Gaussian half-space mass.** For `Γ ≥ 0`, any matrix `A`, `u` and `b`,
`gaussCov A Γ {x | uᵀx ≤ b} = N(0, q)(-∞, b]` with `q = ∑_r (∑_s u_s A⁻¹_{sr})² Γ_r = uᵀA⁻¹ΓA⁻ᵀu`. -/
theorem gaussCov_real_halfSpace [DecidableEq State] (A : Matrix State State ℝ) (Γ : State → ℝ)
    (hΓ : ∀ s, 0 ≤ Γ s) (u : State → ℝ) (b : ℝ) :
    (gaussCov A Γ).real {x | ∑ s, u s * x s ≤ b} =
      (gaussianReal 0 ⟨∑ r, (∑ s, u s * A⁻¹ s r) ^ 2 * Γ r,
        sum_nonneg fun r _ ↦ mul_nonneg (sq_nonneg _) (hΓ r)⟩).real (Set.Iic b) := by
  have hH : MeasurableSet {x : State → ℝ | ∑ s, u s * x s ≤ b} :=
    measurableSet_le (by fun_prop) measurable_const
  set c : State → ℝ := fun r ↦ (∑ s, u s * A⁻¹ s r) * Real.sqrt (Γ r) with hc
  have hm : Measurable (fun z : State → ℝ ↦ ∑ r, c r * z r) := by fun_prop
  have hpre : gaussMap A Γ ⁻¹' {x | ∑ s, u s * x s ≤ b} =
      (fun z : State → ℝ ↦ ∑ r, c r * z r) ⁻¹' Set.Iic b := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Iic, gaussMap, mulVec, dotProduct, hc]
    rw [show ∑ s, u s * ∑ r, A⁻¹ s r * (Real.sqrt (Γ r) * z r) =
        ∑ r, (∑ s, u s * A⁻¹ s r) * Real.sqrt (Γ r) * z r by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun s _ ↦ by ring]
  rw [gaussCov, map_measureReal_apply (measurable_gaussMap A Γ) hH, hpre,
    ← map_measureReal_apply hm measurableSet_Iic]
  have := stdGaussianPi_map_sum_mul (ι := State) c
  simp only [stdGaussianPi] at this
  rw [this]
  congr 3
  exact Finset.sum_congr rfl fun r _ ↦ by rw [hc, mul_pow, Real.sq_sqrt (hΓ r)]

/-- `N(0, q)(-∞, b] = Φ(b/√q)` for `q > 0`. -/
theorem gaussianReal_real_Iic_eq_stdCDF {q : NNReal} (hq : 0 < (q : ℝ)) (b : ℝ) :
    (gaussianReal 0 q).real (Set.Iic b) = stdCDF (b / Real.sqrt q) := by
  set σ := Real.sqrt q with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hq
  have hmap : (gaussianReal 0 1).map (σ * ·) = gaussianReal 0 q := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [hσ, Real.sq_sqrt hq.le]
  rw [← hmap, map_measureReal_apply (by fun_prop) measurableSet_Iic, ← gaussianReal_real_Iic]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic]
  rw [le_div_iff₀ hσ0, mul_comm]

/-- The quadratic form `uᵀ(X diag(Γ) Xᵀ)u = ∑_r (∑_s u_s X_{sr})² Γ_r`. -/
theorem quadForm_mul_diagonal_mul_transpose [DecidableEq State] (X : Matrix State State ℝ)
    (Γ : State → ℝ) (u : State → ℝ) :
    ∑ s, ∑ s', u s * u s' * (X * diagonal Γ * Xᵀ) s s' = ∑ r, (∑ s, u s * X s r) ^ 2 * Γ r := by
  calc ∑ s, ∑ s', u s * u s' * (X * diagonal Γ * Xᵀ) s s'
      = ∑ s, ∑ s', ∑ r, u s * X s r * (u s' * X s' r) * Γ r := by
        simp_rw [mul_diagonal_mul_transpose_apply, Finset.mul_sum]
        exact sum_congr rfl fun s _ ↦ sum_congr rfl fun s' _ ↦ sum_congr rfl fun r _ ↦ by ring
    _ = ∑ s, ∑ r, ∑ s', u s * X s r * (u s' * X s' r) * Γ r :=
        sum_congr rfl fun s _ ↦ Finset.sum_comm
    _ = ∑ r, ∑ s, ∑ s', u s * X s r * (u s' * X s' r) * Γ r := Finset.sum_comm
    _ = ∑ r, (∑ s, u s * X s r) ^ 2 * Γ r := by
        refine sum_congr rfl fun r _ ↦ ?_
        rw [sq, sum_mul_sum, sum_mul]
        exact sum_congr rfl fun s _ ↦ by rw [sum_mul]

/-- **Lower bound for the projected variance.** If `A` is invertible and `g ≤ Γ_r` for all `r`,
`g (∑_s |u_s|)² ≤ (|S| R² + 1) ∑_r (∑_s u_s A⁻¹_{sr})² Γ_r` with `R = ∑_{r,s} |A_{rs}|`. -/
theorem mul_sq_sum_abs_le_quadForm [DecidableEq State] (A : Matrix State State ℝ)
    (hA : IsUnit A.det) (Γ : State → ℝ) {g : ℝ} (hg0 : 0 ≤ g) (hg : ∀ r, g ≤ Γ r)
    (u : State → ℝ) :
    g * (∑ s, |u s|) ^ 2 ≤ ((Fintype.card State : ℝ) * (∑ r, ∑ s, |A r s|) ^ 2 + 1) *
      ∑ r, (∑ s, u s * A⁻¹ s r) ^ 2 * Γ r := by
  set w : State → ℝ := vecMul u A⁻¹ with hw
  set R := ∑ r, ∑ s, |A r s| with hR
  set W := ∑ r, |w r| with hW
  have hwr : ∀ r, w r = ∑ s, u s * A⁻¹ s r := fun r ↦ by simp [hw, vecMul, dotProduct]
  have hu : u = vecMul w A := by
    rw [hw, vecMul_vecMul, nonsing_inv_mul _ hA, vecMul_one]
  have hR0 : 0 ≤ R := sum_nonneg fun r _ ↦ sum_nonneg fun s _ ↦ abs_nonneg _
  have hW0 : 0 ≤ W := sum_nonneg fun r _ ↦ abs_nonneg _
  -- `∑|u| ≤ W R`
  have hU : ∑ s, |u s| ≤ W * R := by
    calc ∑ s, |u s| = ∑ s, |∑ r, w r * A r s| := by
          refine sum_congr rfl fun s _ ↦ ?_
          conv_lhs => rw [hu]
          simp [vecMul, dotProduct]
      _ ≤ ∑ s, ∑ r, W * |A r s| := by
          refine sum_le_sum fun s _ ↦ (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ ↦ ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right
            (single_le_sum (f := fun r ↦ |w r|) (fun r _ ↦ abs_nonneg _) (mem_univ r))
            (abs_nonneg _)
      _ = W * R := by
          rw [hR, Finset.sum_comm, Finset.mul_sum]
          exact sum_congr rfl fun r _ ↦ by rw [Finset.mul_sum]
  have hU0 : 0 ≤ ∑ s, |u s| := sum_nonneg fun s _ ↦ abs_nonneg _
  have hWsq : W ^ 2 ≤ (Fintype.card State : ℝ) * ∑ r, w r ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset State)) (f := fun r ↦ |w r|)
    simpa [sq_abs] using this
  have hq : g * ∑ r, w r ^ 2 ≤ ∑ r, (∑ s, u s * A⁻¹ s r) ^ 2 * Γ r := by
    rw [Finset.mul_sum]
    refine sum_le_sum fun r _ ↦ ?_
    rw [← hwr r, mul_comm]
    exact mul_le_mul_of_nonneg_left (hg r) (sq_nonneg _)
  have hq0 : 0 ≤ ∑ r, (∑ s, u s * A⁻¹ s r) ^ 2 * Γ r :=
    sum_nonneg fun r _ ↦ mul_nonneg (sq_nonneg _) (hg0.trans (hg r))
  calc g * (∑ s, |u s|) ^ 2 ≤ g * (W * R) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hU0 hU 2) hg0
    _ = R ^ 2 * (g * W ^ 2) := by ring
    _ ≤ R ^ 2 * (g * ((Fintype.card State : ℝ) * ∑ r, w r ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWsq hg0) (sq_nonneg _)
    _ = (Fintype.card State : ℝ) * R ^ 2 * (g * ∑ r, w r ^ 2) := by ring
    _ ≤ (Fintype.card State : ℝ) * R ^ 2 * ∑ r, (∑ s, u s * A⁻¹ s r) ^ 2 * Γ r :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ ≤ _ := by nlinarith

/-! ## Data side: Chen–Shao for the projected statistic -/

section DataSide

variable [DecidableEq State]

omit [DecidableEq State] in
/-- The product law `∏ᵢ tupleProb(ωᵢ)` of `BerryEsseenStein` is `pathWeight`. -/
theorem pexp_tupleProb_eq (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {T : ℕ} (F : (Fin T → Tuple State Action) → ℝ) :
    pexp (X := fun _ : Fin T ↦ Tuple State Action) (fun _ ↦ tupleProb M π μ) F =
      ∑ ω, pathWeight M π μ ω * F ω := rfl

/-- `uᵀlinPart = ∑ᵢ uᵀlinSummandᵢ(ωᵢ)`. -/
theorem sum_mul_linPart_eq (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) {T : ℕ} (u : State → ℝ)
    (ω : Fin T → Tuple State Action) :
    ∑ s, u s * linPart M π μ η₀ ω s =
      ∑ i : Fin T, ∑ s, u s * linSummand M π μ η₀ T i (ω i) s := by
  rw [linPart_eq_sum]
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- `E(uᵀlinPart)² = uᵀΛ_Tu`. -/
theorem sum_pathWeight_mul_sq_proj_linPart (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (T : ℕ)
    (u : State → ℝ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * (∑ s, u s * linPart M π μ η₀ ω s) ^ 2 =
      ∑ s, ∑ s', u s * u s' * linCov M π μ η₀ T s s' := by
  simp_rw [sq, sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun s' _ ↦ ?_
  rw [← sum_pathWeight_linPart_mul_linPart M π μ η₀ T s s', Finset.mul_sum]
  exact sum_congr rfl fun ω _ ↦ by ring

/-- **Chen–Shao bound for a fixed direction.** For `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`, `T ≥ 1`,
every `V₀`, `u`, `b`, if `q_T = uᵀΛ_Tu > 0` then, with `σ_T = √q_T`, `U = ∑_s |u_s|` and
`r = T^{-1/3}`,
`|P(uᵀ√TΔ̄_T ≤ b) − Φ(b/σ_T)| ≤ (U/σ_T)(28 K_β B + K_E) r + (U/σ_T)² K_CS r`. -/
theorem abs_lawProb_halfSpace_sub_stdCDF_le [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T)
    (u : State → ℝ) (b : ℝ) (hq : 0 < ∑ s, ∑ s', u s * u s' * linCov M π μ η₀ T s s') :
    |lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ b} -
        stdCDF (b / Real.sqrt (∑ s, ∑ s', u s * u s' * linCov M π μ η₀ T s s'))| ≤
      (∑ s, |u s|) / Real.sqrt (∑ s, ∑ s', u s * u s' * linCov M π μ η₀ T s s') *
          (28 * (linWeightConst M μmin η₀ * tdNoiseBound M π) +
            linRemainderConst M π V₀ μmin η₀) * (T : ℝ) ^ (-(1 / 3 : ℝ)) +
        ((∑ s, |u s|) / Real.sqrt (∑ s, ∑ s', u s * u s' * linCov M π μ η₀ T s s')) ^ 2 *
          looChenShaoConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  set q := ∑ s, ∑ s', u s * u s' * linCov M π μ η₀ T s s' with hqdef
  set σ := Real.sqrt q with hσdef
  set U := ∑ s, |u s| with hUdef
  set r := (T : ℝ) ^ (-(1 / 3 : ℝ)) with hrdef
  set Kβ := linWeightConst M μmin η₀
  set B := tdNoiseBound M π
  set KE := linRemainderConst M π V₀ μmin η₀
  set KC := looChenShaoConst M π V₀ μmin η₀
  have hσ : 0 < σ := Real.sqrt_pos.2 hq
  have hσ2 : σ ^ 2 = q := Real.sq_sqrt hq.le
  have hU0 : 0 ≤ U := sum_nonneg fun s _ ↦ abs_nonneg _
  have hK0 : 0 ≤ Kβ := linWeightConst_nonneg M hμmin0 h0
  have hB0 : 0 < B := tdNoiseBound_pos M π
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let X : Fin T → Type := fun _ ↦ Tuple State Action
  let p : ∀ i : Fin T, X i → ℝ := fun _ ↦ tupleProb M π μ
  let ξ : ∀ i : Fin T, X i → ℝ := fun i x ↦ ∑ s, u s * linSummand M π μ η₀ T i x s
  let Δ : (∀ i : Fin T, X i) → ℝ := fun ω ↦
    ∑ s, u s * (scaledError M π η₀ V₀ ω s - linPart M π μ η₀ ω s)
  let xs : ∀ i : Fin T, X i := fun _ ↦ Classical.arbitrary _
  have hp0 : ∀ i x, 0 ≤ p i x := fun _ x ↦ tupleProb_nonneg M π μ x
  have hp1 : ∀ i, ∑ x, p i x = 1 := fun _ ↦ sum_tupleProb M π μ
  have hmean : ∀ i, ∑ x, p i x * ξ i x = 0 := by
    intro i
    simp only [p, ξ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine sum_eq_zero fun s _ ↦ ?_
    have h := sum_tupleProb_mul_linSummand M π μ η₀ T i s
    rw [show ∑ x, tupleProb M π μ x * (u s * linSummand M π μ η₀ T i x s) =
        u s * ∑ x, tupleProb M π μ x * linSummand M π μ η₀ T i x s by
      rw [Finset.mul_sum]; exact sum_congr rfl fun x _ ↦ by ring, h, mul_zero]
  have hsum : ∀ ω, sumStat ξ ω = ∑ s, u s * linPart M π μ η₀ ω s := fun ω ↦
    (sum_mul_linPart_eq M π μ η₀ u ω).symm
  have hW2 : pexp p (fun ω ↦ sumStat ξ ω ^ 2) = q := by
    rw [pexp_tupleProb_eq]
    simp_rw [hsum]
    exact sum_pathWeight_mul_sq_proj_linPart M π μ η₀ T u
  have hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = σ ^ 2 := by
    rw [hσ2, ← hW2, pexp_sumStat_sq hp1 hmean]
  have hCS := chenShao_nonlinear_of_var hp0 hp1 hmean hσ hvar Δ
    (fun i ω ↦ Δ (Function.update ω i (xs i))) (fun i ω b ↦ by simp only [Function.update_idem]) b
  -- the probability
  have hP : pexp p (fun ω ↦ if sumStat ξ ω + Δ ω ≤ b then 1 else 0) =
      lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ b} := by
    rw [pexp_tupleProb_eq, lawProb]
    refine sum_congr rfl fun ω _ ↦ ?_
    congr 1
    have e : sumStat ξ ω + Δ ω = ∑ s, u s * scaledError M π η₀ V₀ ω s := by
      rw [hsum]
      simp only [Δ, ← sum_add_distrib]
      exact sum_congr rfl fun s _ ↦ by ring
    rw [e, Set.indicator_apply]
    simp only [Set.mem_setOf_eq]
  rw [hP, gaussianReal_real_Iic] at hCS
  -- the three error terms
  have hξ : ∀ i x, |ξ i x| ≤ U * ((Real.sqrt T)⁻¹ * (Kβ * B)) := fun i x ↦
    abs_proj_linSummand_le M π μ h0 h1 hμmin0 hμmin T i x u
  set m := U * ((Real.sqrt T)⁻¹ * (Kβ * B)) with hm
  have hm_le : m ≤ U * (Kβ * B) * r := by
    rw [hm, show U * ((Real.sqrt T)⁻¹ * (Kβ * B)) = U * (Kβ * B) * (Real.sqrt T)⁻¹ by ring]
    exact mul_le_mul_of_nonneg_left (inv_sqrt_le_rpow hT) (mul_nonneg hU0 (mul_nonneg hK0 hB0.le))
  have hβ : ∑ i, ∑ x, p i x * |ξ i x| ^ 3 ≤ m * σ ^ 2 := by
    rw [← hvar, Finset.mul_sum]
    refine sum_le_sum fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine sum_le_sum fun x _ ↦ ?_
    rw [show |ξ i x| ^ 3 = |ξ i x| * ξ i x ^ 2 by rw [pow_succ', sq_abs],
      show m * (p i x * ξ i x ^ 2) = p i x * (m * ξ i x ^ 2) by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hξ i x) (sq_nonneg _))
      (hp0 i x)
  have hWΔ : pexp p (fun ω ↦ |sumStat ξ ω * Δ ω|) ≤ σ * (U * (KE * r)) := by
    refine (pexp_abs_mul_le_sqrt hp0 _ _).trans ?_
    rw [hW2]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    exact weightedL2_proj_scaledError_sub_linPart_le M π μ h0 h1 V₀ hμmin0 hμmin hT u
  have hloo : ∑ i, pexp p (fun ω ↦ |ξ i (ω i) * (Δ ω - Δ (Function.update ω i (xs i)))|) ≤
      U ^ 2 * KC * r := by
    refine le_of_eq_of_le ?_ (sum_looChenShao_le M π μ h0 h1 V₀ hμmin0 hμmin hT u xs)
    refine sum_congr rfl fun i _ ↦ ?_
    rw [pexp_tupleProb_eq]
    refine sum_congr rfl fun ω _ ↦ ?_
    have e : Δ ω - Δ (Function.update ω i (xs i)) =
        ∑ s, u s * looRemainder M π μ η₀ V₀ i (xs i) ω s := by
      simp only [Δ, looRemainder, Pi.sub_apply, ← sum_sub_distrib]
      exact sum_congr rfl fun s _ ↦ by ring
    rw [e]
  have hσ3 : 0 < σ ^ 3 := by positivity
  have hσ2p : 0 < σ ^ 2 := by positivity
  have t1 : 28 * (∑ i, ∑ x, p i x * |ξ i x| ^ 3) / σ ^ 3 ≤ 28 * (U * (Kβ * B) * r) / σ := by
    rw [div_le_div_iff₀ hσ3 hσ]
    have : 28 * (∑ i, ∑ x, p i x * |ξ i x| ^ 3) * σ ≤ 28 * (m * σ ^ 2) * σ := by gcongr
    calc 28 * (∑ i, ∑ x, p i x * |ξ i x| ^ 3) * σ ≤ 28 * (m * σ ^ 2) * σ := this
      _ = 28 * m * σ ^ 3 := by ring
      _ ≤ 28 * (U * (Kβ * B) * r) * σ ^ 3 := by gcongr
  have t2 : pexp p (fun ω ↦ |sumStat ξ ω * Δ ω|) / σ ^ 2 ≤ U * (KE * r) / σ := by
    rw [div_le_div_iff₀ hσ2p hσ]
    calc pexp p (fun ω ↦ |sumStat ξ ω * Δ ω|) * σ ≤ σ * (U * (KE * r)) * σ := by gcongr
      _ = U * (KE * r) * σ ^ 2 := by ring
  have t3 : (∑ i, pexp p (fun ω ↦ |ξ i (ω i) * (Δ ω - Δ (Function.update ω i (xs i)))|)) /
      σ ^ 2 ≤ U ^ 2 * KC * r / σ ^ 2 := by gcongr
  refine hCS.trans ?_
  calc 28 * (∑ i, ∑ x, p i x * |ξ i x| ^ 3) / σ ^ 3 +
        pexp p (fun ω ↦ |sumStat ξ ω * Δ ω|) / σ ^ 2 +
        (∑ i, pexp p (fun ω ↦ |ξ i (ω i) * (Δ ω - Δ (Function.update ω i (xs i)))|)) / σ ^ 2
      ≤ 28 * (U * (Kβ * B) * r) / σ + U * (KE * r) / σ + U ^ 2 * KC * r / σ ^ 2 := by
        linarith
    _ = U / σ * (28 * (Kβ * B) + KE) * r + (U / σ) ^ 2 * KC * r := by
        field_simp

end DataSide

/-! ## Assembly -/

section Assembly

variable [DecidableEq State]

theorem le_one_add_sq (x : ℝ) : x ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (x - 1)]

/-- Variance step: `|Φ(b/√q_T) − Φ(b/√q)| ≤ 2|q_T − q|/q` for `q_T, q > 0`. -/
theorem abs_stdCDF_div_sqrt_sub_le (b : ℝ) {qT q : ℝ} (hqT : 0 < qT) (hq : 0 < q) :
    |stdCDF (b / Real.sqrt qT) - stdCDF (b / Real.sqrt q)| ≤ 2 * |qT - q| / q := by
  have h := abs_stdCDF_div_sub_le b (Real.sqrt_pos.2 hqT) (Real.sqrt_pos.2 hq)
  rw [Real.sq_sqrt hqT.le, Real.sq_sqrt hq.le,
    show qT / q - 1 = (qT - q) / q by field_simp, abs_div, abs_of_pos hq] at h
  rw [mul_div_assoc]
  exact h

/-- A closed half-space with zero normal is `univ` or `∅`; both laws agree on it. -/
theorem lawProb_halfSpace_zero_sub_gaussCov (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) (A : Matrix State State ℝ) (Γ : State → ℝ) (b : ℝ) :
    lawProb M π μ η₀ V₀ T {x | ∑ s, (0 : State → ℝ) s * x s ≤ b} -
      (gaussCov A Γ).real {x | ∑ s, (0 : State → ℝ) s * x s ≤ b} = 0 := by
  by_cases hb : 0 ≤ b
  · have hset : {x : State → ℝ | ∑ s, (0 : State → ℝ) s * x s ≤ b} = Set.univ := by
      ext x; simp [hb]
    rw [hset, lawProb_univ, probReal_univ, sub_self]
  · have hset : {x : State → ℝ | ∑ s, (0 : State → ℝ) s * x s ≤ b} = ∅ := by
      ext x; simp [hb]
    rw [hset, measureReal_empty]
    simp [lawProb]

/-- **Theorem 7.11 on closed half-spaces (corrected covariance), library form.** For every
instance with full-support `μ` and `Γ_true ≻ 0`, every `0 < η₀ ≤ 1` and every `V₀`, there is
`K > 0` (depending on the instance, `η₀` and `V₀`) such that for all `T ≥ 1`, all `u : State → ℝ`
and all `b : ℝ`,
`|P(uᵀ√TΔ̄_T ≤ b) − N(0, A⁻¹ diag(Γ_true) A⁻ᵀ){x | uᵀx ≤ b}| ≤ K T^{-1/3}`. -/
theorem abs_lawProb_halfSpace_sub_gaussCov_le [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ (u : State → ℝ) (b : ℝ),
      |lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ b} -
          (gaussCov (tdA M π μ) (trueGamma M π μ)).real {x | ∑ s, u s * x s ≤ b}| ≤
        K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  -- instance constants
  set μmin := Finset.univ.inf' Finset.univ_nonempty μ.prob with hμmindef
  have hμmin0 : 0 < μmin := (Finset.lt_inf'_iff _).2 fun s _ ↦ hμ s
  have hμmin : ∀ s, μmin ≤ μ.prob s := fun s ↦ Finset.inf'_le _ (mem_univ s)
  set Γ := trueGamma M π μ with hΓdef
  set g := Finset.univ.inf' Finset.univ_nonempty Γ with hgdef
  have hg0 : 0 < g := (Finset.lt_inf'_iff _).2 fun s _ ↦ hΓ s
  have hg : ∀ s, g ≤ Γ s := fun s ↦ Finset.inf'_le _ (mem_univ s)
  set A := tdA M π μ with hAdef
  have hA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 (tdA_isUnit M π μ hμmin0 hμmin)
  set R := ∑ r, ∑ s, |A r s|
  set D := (Fintype.card State : ℝ) * R ^ 2 + 1 with hDdef
  have hD : 0 < D := by positivity
  set c := g / D with hcdef
  have hc : 0 < c := div_pos hg0 hD
  set Λ := A⁻¹ * diagonal Γ * (A⁻¹)ᵀ with hΛdef
  set Kβ := linWeightConst M μmin η₀
  set B := tdNoiseBound M π
  set KE := linRemainderConst M π V₀ μmin η₀
  set KC := looChenShaoConst M π V₀ μmin η₀
  set KL := linCovConst M π μ μmin η₀
  set K := (1 + 2 / c) * (28 * |Kβ * B| + |KE|) + 2 / c * |KC| + 2 / c * |KL| + 1 with hKdef
  have hK1 : 2 / c * |KL| + 1 ≤ K := by
    have : 0 ≤ (1 + 2 / c) * (28 * |Kβ * B| + |KE|) + 2 / c * |KC| := by positivity
    linarith
  refine ⟨K, by positivity, fun T hT u b ↦ ?_⟩
  set r := (T : ℝ) ^ (-(1 / 3 : ℝ)) with hrdef
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set H := {x : State → ℝ | ∑ s, u s * x s ≤ b} with hHdef
  set U := ∑ s, |u s| with hUdef
  have hU0 : 0 ≤ U := sum_nonneg fun s _ ↦ abs_nonneg _
  -- the zero direction
  rcases hU0.lt_or_eq with hUpos | hUzero
  swap
  · have hu : u = 0 := by
      funext s
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ ↦ abs_nonneg (u s))).1 hUzero.symm s
        (mem_univ s)
      simpa using this
    rw [hHdef, hu, lawProb_halfSpace_zero_sub_gaussCov, abs_zero]
    positivity
  -- the trivial bound
  have htriv : |lawProb M π μ η₀ V₀ T H - (gaussCov A Γ).real H| ≤ 1 := by
    rw [abs_le]
    have := lawProb_nonneg M π μ η₀ V₀ T H
    have := lawProb_le_one M π μ η₀ V₀ T H
    have : 0 ≤ (gaussCov A Γ).real H := measureReal_nonneg
    have : (gaussCov A Γ).real H ≤ 1 := measureReal_le_one
    constructor <;> linarith
  -- the Gaussian variance `q = uᵀΛu` and its lower bound
  set q := ∑ s, ∑ s', u s * u s' * Λ s s' with hqdef
  have hqform : q = ∑ r, (∑ s, u s * A⁻¹ s r) ^ 2 * Γ r :=
    quadForm_mul_diagonal_mul_transpose A⁻¹ Γ u
  have hqlow : c * U ^ 2 ≤ q := by
    have h := mul_sq_sum_abs_le_quadForm A hA Γ hg0.le hg u
    rw [← hqform] at h
    rw [hcdef, div_mul_eq_mul_div, div_le_iff₀ hD]
    linarith
  have hq : 0 < q := lt_of_lt_of_le (by positivity) hqlow
  have hGauss : (gaussCov A Γ).real H = stdCDF (b / Real.sqrt q) := by
    rw [hHdef, gaussCov_real_halfSpace A Γ (fun s ↦ (hΓ s).le) u b,
      gaussianReal_real_Iic_eq_stdCDF (by simpa [← hqform] using hq)]
    simp [← hqform]
  -- the finite-`T` variance and its comparison
  set qT := ∑ s, ∑ s', u s * u s' * linCov M π μ η₀ T s s' with hqTdef
  have hqTq : |qT - q| ≤ U ^ 2 * KL * r := by
    have h := abs_quadForm_linCov_sub_le M π μ h0 h1 hμmin0 hμmin hT u
    have e : qT - q = ∑ s, ∑ s', u s * u s' * (linCov M π μ η₀ T s s' - Λ s s') := by
      rw [hqTdef, hqdef, ← sum_sub_distrib]
      refine sum_congr rfl fun s _ ↦ ?_
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun s' _ ↦ by ring
    rw [e]
    exact h
  by_cases hsmall : |KL| * r ≤ c / 2
  swap
  · -- small `T`: the trivial bound
    push_neg at hsmall
    refine htriv.trans ?_
    have : 1 < 2 / c * |KL| * r := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, lt_div_iff₀ hc]; linarith
    calc (1 : ℝ) ≤ 2 / c * |KL| * r := this.le
      _ ≤ (2 / c * |KL| + 1) * r := by rw [add_mul, one_mul]; linarith
      _ ≤ K * r := mul_le_mul_of_nonneg_right hK1 hr0
  -- large `T`: `q_T ≥ c U²/2`
  have hqT_low : c * U ^ 2 / 2 ≤ qT := by
    have h1' : U ^ 2 * KL * r ≤ U ^ 2 * (c / 2) := by
      calc U ^ 2 * KL * r ≤ U ^ 2 * (|KL| * r) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (le_abs_self _) hr0) (sq_nonneg _)
        _ ≤ U ^ 2 * (c / 2) := mul_le_mul_of_nonneg_left hsmall (sq_nonneg _)
    have := (abs_le.1 hqTq).1
    linarith
  have hqT : 0 < qT := lt_of_lt_of_le (by positivity) hqT_low
  have hCS := abs_lawProb_halfSpace_sub_stdCDF_le M π μ h0 h1 V₀ hμmin0 hμmin hT u b hqT
  rw [← hqTdef] at hCS
  set ρ := U / Real.sqrt qT with hρdef
  have hρ0 : 0 ≤ ρ := div_nonneg hU0 (Real.sqrt_nonneg _)
  have hρ2 : ρ ^ 2 ≤ 2 / c := by
    rw [hρdef, div_pow, Real.sq_sqrt hqT.le, div_le_div_iff₀ hqT hc]
    linarith
  have hρ : ρ ≤ 1 + 2 / c := by linarith [le_one_add_sq ρ]
  have hvar : |stdCDF (b / Real.sqrt qT) - stdCDF (b / Real.sqrt q)| ≤ 2 / c * |KL| * r := by
    refine (abs_stdCDF_div_sqrt_sub_le b hqT hq).trans ?_
    rw [div_le_iff₀ hq]
    calc 2 * |qT - q| ≤ 2 * (U ^ 2 * KL * r) := by linarith
      _ ≤ 2 * (U ^ 2 * (|KL| * r)) := by
          rw [mul_assoc (U ^ 2)]
          gcongr
          exact le_abs_self _
      _ = 2 / c * |KL| * r * (c * U ^ 2) := by field_simp
      _ ≤ 2 / c * |KL| * r * q := by gcongr
  have hX : ρ * (28 * (Kβ * B) + KE) * r ≤ (1 + 2 / c) * (28 * |Kβ * B| + |KE|) * r := by
    refine mul_le_mul_of_nonneg_right ?_ hr0
    have hX1 : 28 * (Kβ * B) + KE ≤ 28 * |Kβ * B| + |KE| := by
      have := le_abs_self (Kβ * B); have := le_abs_self KE; linarith
    calc ρ * (28 * (Kβ * B) + KE) ≤ ρ * (28 * |Kβ * B| + |KE|) :=
          mul_le_mul_of_nonneg_left hX1 hρ0
      _ ≤ (1 + 2 / c) * (28 * |Kβ * B| + |KE|) :=
          mul_le_mul_of_nonneg_right hρ (by positivity)
  have hY : ρ ^ 2 * KC * r ≤ 2 / c * |KC| * r := by
    rw [mul_assoc, mul_assoc]
    calc ρ ^ 2 * (KC * r) ≤ ρ ^ 2 * (|KC| * r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hr0)
            (sq_nonneg _)
      _ ≤ 2 / c * (|KC| * r) := mul_le_mul_of_nonneg_right hρ2 (by positivity)
  rw [hGauss]
  calc |lawProb M π μ η₀ V₀ T H - stdCDF (b / Real.sqrt q)|
      ≤ |lawProb M π μ η₀ V₀ T H - stdCDF (b / Real.sqrt qT)| +
          |stdCDF (b / Real.sqrt qT) - stdCDF (b / Real.sqrt q)| := abs_sub_le _ _ _
    _ ≤ (ρ * (28 * (Kβ * B) + KE) * r + ρ ^ 2 * KC * r) + 2 / c * |KL| * r :=
        add_le_add hCS hvar
    _ ≤ ((1 + 2 / c) * (28 * |Kβ * B| + |KE|) * r + 2 / c * |KC| * r) + 2 / c * |KL| * r := by
        linarith
    _ ≤ K * r := by
        have e : K * r = (1 + 2 / c) * (28 * |Kβ * B| + |KE|) * r + 2 / c * |KC| * r +
            2 / c * |KL| * r + r := by rw [hKdef]; ring
        rw [e]; linarith

end Assembly

end StatisticalRL.Ch7Rest.TDInference

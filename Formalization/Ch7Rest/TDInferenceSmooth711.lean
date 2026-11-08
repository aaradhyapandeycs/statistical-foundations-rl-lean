import Formalization.Ch7Rest.TDInferencePRRemainder711
import Formalization.Probability.WeightedL2
import Formalization.Probability.LindebergFinite

/-!
# Theorem 7.11 support: smooth-test-function Gaussian approximation of
Polyak–Ruppert-averaged TD

**Partial result, not a restricted variant of Theorem 7.11, not counted in the named-result
ledger.** Source objects: `chapters/inference.tex` i.i.d. tuples :52–66, TD update :70–75,
Polyak–Ruppert average and `Δ̄_T` :80–89, `Λ⋆ = A⁻¹ΓA⁻ᵀ`, `A`, `Γ` :104–117; printed theorem
`thm:Berry-Esseen-linear` :132–141 (refuted in Lean as printed, `docs/SOURCE-ISSUES.md#C43`).

Main export `scaledError_smooth_gaussian_le`: for every `T ≥ 1` and every `C²` test function `f`
on `State → ℝ` (sup norm) with `‖Df‖ ≤ L₁` and `L₂`-Lipschitz `D²f`,
`|E f(√T Δ̄_T) − E f(Z)| ≤ L₁ K T^{-1/6} + L₂ C T^{-1/2}`, `Z ∼ gaussCov A Γ_true`, with the
explicit constants `smoothRemainderConst` (`K`) and `smoothLindebergConst` (`C`).

Route: `√T Δ̄_T = W_T + R_T` with `W_T = prGaussPart` an i.i.d. sum (`prGaussPart_eq_smul_sum`);
`|E f(√TΔ̄_T) − E f(W_T)| ≤ L₁ ∑_s ‖R_T(s)‖_{L²}` (bounded gradient + Cauchy–Schwarz, M3 remainder
bound); `|E f(W_T) − E f(Z)|` by the finite i.i.d. Lindeberg theorem `lindeberg_iid`.

Auxiliary exports: `tdY`, `tdGaussFactor`, `prGaussPart_eq_smul_sum`, `gaussMap_eq_mulVec`,
`integral_gaussCov_eq`, `sum_tupleProb_mul_tdY`, `sum_tupleProb_mul_tdY_mul`,
`norm_tdY_le`, `integral_norm_tdGaussFactor_mulVec_pow_three_le`,
`abs_sum_mul_sub_sum_mul_le_weightedL2`, `sum_pathWeight_mul_prGaussPart_smooth_le`.
-/

open MeasureTheory ProbabilityTheory Matrix
open StatisticalRL.Probability StatisticalRL.Analysis

namespace StatisticalRL.Ch7Rest.TDInference

variable {State Action : Type} [Fintype State] [Fintype Action]

/-! ## The i.i.d. summand of `W_T` and the Gaussian factor -/

/-- The i.i.d. summand `Y(x) = −A⁻¹ ξ(x) e_{s(x)}` of `W_T = T^{-1/2} ∑_k Y(ω_k)`. -/
noncomputable def tdY [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (x : Tuple State Action) :
    State → ℝ :=
  -((tdA M π μ)⁻¹ *ᵥ noiseVec M π x)

/-- The factor `L = A⁻¹ diag(√Γ_true)`, so that `gaussCov A Γ_true` is the law of `L Z`. -/
noncomputable def tdGaussFactor [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) : Matrix State State ℝ :=
  (tdA M π μ)⁻¹ * Matrix.diagonal fun s ↦ √(trueGamma M π μ s)

theorem trueGamma_nonneg (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (s : State) : 0 ≤ trueGamma M π μ s :=
  mul_nonneg (μ.prob_nonneg s) (FiniteDistribution.expectation_nonneg _ fun _ ↦
    FiniteDistribution.expectation_nonneg _ fun _ ↦ sq_nonneg _)

theorem prGaussPart_eq_smul_sum [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ}
    (ω : Fin T → Tuple State Action) :
    prGaussPart M π μ ω = (√(T : ℝ))⁻¹ • ∑ k, tdY M π μ (ω k) := by
  simp only [prGaussPart, prNoiseSum, tdY, Matrix.mulVec_sum, Finset.sum_neg_distrib, smul_neg]

theorem gaussMap_eq_mulVec [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (z : State → ℝ) :
    gaussMap (tdA M π μ) (trueGamma M π μ) z = tdGaussFactor M π μ *ᵥ z := by
  rw [tdGaussFactor, ← Matrix.mulVec_mulVec, gaussMap]
  congr 1
  ext s
  rw [Matrix.mulVec_diagonal]

/-- Integrals against `gaussCov A Γ_true` are integrals of `f (L z)` against the standard
Gaussian (for measurable `f`; no integrability needed for the identity). -/
theorem integral_gaussCov_eq [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {f : (State → ℝ) → ℝ}
    (hf : Measurable f) :
    ∫ x, f x ∂(gaussCov (tdA M π μ) (trueGamma M π μ)) =
      ∫ z, f (tdGaussFactor M π μ *ᵥ z) ∂(stdGaussianPi State) := by
  rw [gaussCov, integral_map (measurable_gaussMap _ _).aemeasurable hf.aestronglyMeasurable]
  simp_rw [gaussMap_eq_mulVec]

/-- `E Y = 0`. -/
theorem sum_tupleProb_mul_tdY [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (i : State) :
    ∑ x, tupleProb M π μ x * tdY M π μ x i = 0 := by
  simp only [tdY, Pi.neg_apply, Matrix.mulVec, dotProduct, mul_neg, Finset.sum_neg_distrib,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [show ∀ (u : State) (x : Tuple State Action), tupleProb M π μ x *
      ((tdA M π μ)⁻¹ i u * noiseVec M π x u) =
      (tdA M π μ)⁻¹ i u * (tupleProb M π μ x * noiseVec M π x u) from fun u x ↦ by ring,
    ← Finset.mul_sum, sum_tupleProb_mul_noiseVec, mul_zero, Finset.sum_const_zero, neg_zero]

/-- `E Y Yᵀ = L Lᵀ` with `L = A⁻¹ diag(√Γ_true)` (uses `Γ_true ≥ 0`). -/
theorem sum_tupleProb_mul_tdY_mul [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (i j : State) :
    ∑ x, tupleProb M π μ x * (tdY M π μ x i * tdY M π μ x j) =
      (tdGaussFactor M π μ * (tdGaussFactor M π μ).transpose) i j := by
  set B := (tdA M π μ)⁻¹
  have e : ∀ x, tupleProb M π μ x * (tdY M π μ x i * tdY M π μ x j) =
      ∑ u, ∑ v, B i u * B j v * (tupleProb M π μ x * (noiseVec M π x u * noiseVec M π x v)) := by
    intro x
    have hk : ∀ k, tdY M π μ x k = -∑ u, B k u * noiseVec M π x u := fun k ↦ by
      simp [tdY, Matrix.mulVec, dotProduct, B]
    rw [hk, hk, neg_mul_neg, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ ↦ by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ ↦ by ring
  simp_rw [e]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Tuple State Action))) (t := Finset.univ),
    ← Finset.mul_sum, sum_tupleProb_mul_noiseVec_mul]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [tdGaussFactor, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.mul_diagonal, B]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  have := Real.mul_self_sqrt (trueGamma_nonneg M π μ u)
  linear_combination (-((tdA M π μ)⁻¹ i u * (tdA M π μ)⁻¹ j u)) * this

/-! ## Moment bounds -/

theorem norm_noiseVec_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (x : Tuple State Action) :
    ‖noiseVec M π x‖ ≤ tdNoiseBound M π := by
  rw [noiseVec, Pi.norm_single, Real.norm_eq_abs]
  exact abs_tdNoise_le M π x

theorem norm_tdY_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {μmin : ℝ}
    (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) (x : Tuple State Action) :
    ‖tdY M π μ x‖ ≤ tdNoiseBound M π / ((1 - M.discount) * μmin) := by
  have hc : 0 < (1 - M.discount) * μmin := mul_pos (by linarith [M.discount_lt_one]) hμmin0
  rw [tdY, norm_neg]
  exact (norm_tdA_inv_mulVec_le M π μ hμmin0 hμmin _).trans
    (div_le_div_of_nonneg_right (norm_noiseVec_le M π x) hc.le)

theorem sum_tupleProb_mul_norm_tdY_pow_three_le [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) :
    ∑ x, tupleProb M π μ x * ‖tdY M π μ x‖ ^ 3 ≤
      (tdNoiseBound M π / ((1 - M.discount) * μmin)) ^ 3 := by
  calc ∑ x, tupleProb M π μ x * ‖tdY M π μ x‖ ^ 3
      ≤ ∑ x, tupleProb M π μ x * (tdNoiseBound M π / ((1 - M.discount) * μmin)) ^ 3 :=
        Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (norm_tdY_le M π μ hμmin0 hμmin x) 3)
          (tupleProb_nonneg M π μ x)
    _ = _ := by rw [← Finset.sum_mul, sum_tupleProb, one_mul]

theorem norm_tdGaussFactor_mulVec_le [DecidableEq State] [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    (z : State → ℝ) :
    ‖tdGaussFactor M π μ *ᵥ z‖ ≤
      √(diagMax (trueGamma M π μ)) / ((1 - M.discount) * μmin) * ‖z‖ := by
  have hc : 0 < (1 - M.discount) * μmin := mul_pos (by linarith [M.discount_lt_one]) hμmin0
  rw [← gaussMap_eq_mulVec, gaussMap]
  refine (norm_tdA_inv_mulVec_le M π μ hμmin0 hμmin _).trans ?_
  rw [div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hc.le
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul (Real.sqrt_le_sqrt
      (Finset.le_sup' (trueGamma M π μ) (Finset.mem_univ s)))
    (abs_apply_le_norm z s) (abs_nonneg _) (Real.sqrt_nonneg _)

theorem integral_norm_tdGaussFactor_mulVec_pow_three_le [DecidableEq State] [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) :
    ∫ z, ‖tdGaussFactor M π μ *ᵥ z‖ ^ 3 ∂(stdGaussianPi State) ≤
      Fintype.card State * (12 * Real.exp (1 / 2)) *
        (√(diagMax (trueGamma M π μ)) / ((1 - M.discount) * μmin)) ^ 3 := by
  have hc : 0 < (1 - M.discount) * μmin := mul_pos (by linarith [M.discount_lt_one]) hμmin0
  set k := √(diagMax (trueGamma M π μ)) / ((1 - M.discount) * μmin)
  have hk : 0 ≤ k := div_nonneg (Real.sqrt_nonneg _) hc.le
  calc ∫ z, ‖tdGaussFactor M π μ *ᵥ z‖ ^ 3 ∂(stdGaussianPi State)
      ≤ ∫ z, k ^ 3 * ‖z‖ ^ 3 ∂(stdGaussianPi State) :=
        integral_mono (integrable_norm_mulVec_pow_three_stdGaussianPi _)
          (integrable_norm_pow_three_stdGaussianPi.const_mul _) fun z ↦ by
            rw [← mul_pow]
            exact pow_le_pow_left₀ (norm_nonneg _)
              (norm_tdGaussFactor_mulVec_le M π μ hμmin0 hμmin z) 3
    _ = k ^ 3 * ∫ z, ‖z‖ ^ 3 ∂(stdGaussianPi State) := integral_const_mul _ _
    _ ≤ k ^ 3 * (Fintype.card State * (12 * Real.exp (1 / 2))) :=
        mul_le_mul_of_nonneg_left integral_norm_pow_three_stdGaussianPi_le (by positivity)
    _ = _ := by ring

/-! ## Remainder transfer -/

/-- For weights `w ≥ 0` with `∑ w = 1` and an `L₁`-Lipschitz `f` on `State → ℝ` (sup norm),
`|E f(X) − E f(W)| ≤ L₁ ∑_s ‖X(s) − W(s)‖_{L²(w)}`. -/
theorem abs_sum_mul_sub_sum_mul_le_weightedL2 {Ω : Type*} [Fintype Ω] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1) {f : (State → ℝ) → ℝ} {L₁ : ℝ}
    (hf : ∀ a b, |f a - f b| ≤ L₁ * ‖a - b‖) (hL₁ : 0 ≤ L₁) (X W : Ω → State → ℝ) :
    |∑ ω, w ω * f (X ω) - ∑ ω, w ω * f (W ω)| ≤
      L₁ * ∑ s, weightedL2 w (fun ω ↦ X ω s - W ω s) := by
  have hnorm : ∀ v : State → ℝ, ‖v‖ ≤ ∑ s, |v s| := fun v ↦
    (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun s _ ↦ abs_nonneg _)).2 fun s ↦ by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun s ↦ |v s|) (fun s _ ↦ abs_nonneg _) (Finset.mem_univ s)
  have hone : weightedL2 w (fun _ ↦ (1 : ℝ)) = 1 := by
    simp [weightedL2, hw1]
  have hcs : ∀ s, ∑ ω, w ω * |X ω s - W ω s| ≤ weightedL2 w (fun ω ↦ X ω s - W ω s) := by
    intro s
    have := sum_mul_mul_le_weightedL2 hw (fun ω ↦ |X ω s - W ω s|) (fun _ ↦ 1)
    simpa [weightedL2_abs, hone] using this
  calc |∑ ω, w ω * f (X ω) - ∑ ω, w ω * f (W ω)|
      = |∑ ω, w ω * (f (X ω) - f (W ω))| := by
        rw [← Finset.sum_sub_distrib]; simp_rw [mul_sub]
    _ ≤ ∑ ω, |w ω * (f (X ω) - f (W ω))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω, w ω * (L₁ * ∑ s, |X ω s - W ω s|) := Finset.sum_le_sum fun ω _ ↦ by
        rw [abs_mul, abs_of_nonneg (hw ω)]
        refine mul_le_mul_of_nonneg_left ((hf _ _).trans ?_) (hw ω)
        exact mul_le_mul_of_nonneg_left (hnorm _) hL₁
    _ = L₁ * ∑ s, ∑ ω, w ω * |X ω s - W ω s| := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun ω _ ↦ by ring
    _ ≤ L₁ * ∑ s, weightedL2 w (fun ω ↦ X ω s - W ω s) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ ↦ hcs s) hL₁

/-! ## Constants -/

/-- The `T^{-1/6}` constant `K = |State|² K_R / ((1−γ) μmin)` (`K_R = prRemainderConst`, which
depends on `V₀` and is polynomial in `1/((1−γ) μmin η₀)`). -/
noncomputable def smoothRemainderConst (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V₀ : State → ℝ) (μmin η₀ : ℝ) : ℝ :=
  Fintype.card State ^ 2 * prRemainderConst M π V₀ μmin η₀ / ((1 - M.discount) * μmin)

/-- The `T^{-1/2}` constant
`C = ((B/a)³ + |State| · 12 e^{1/2} · (√(max_s Γ_true(s))/a)³) / 6`, `a = (1−γ) μmin`,
`B = tdNoiseBound`. -/
noncomputable def smoothLindebergConst [Nonempty State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (μmin : ℝ) : ℝ :=
  ((tdNoiseBound M π / ((1 - M.discount) * μmin)) ^ 3 +
    Fintype.card State * (12 * Real.exp (1 / 2)) *
      (√(diagMax (trueGamma M π μ)) / ((1 - M.discount) * μmin)) ^ 3) / 6

/-! ## Gaussian approximation of `W_T` -/

/-- Lindeberg for `W_T`: `|E f(W_T) − E f(Z)| ≤ L₂ C T^{-1/2}`, `Z ∼ gaussCov A Γ_true`. -/
theorem sum_pathWeight_mul_prGaussPart_smooth_le [DecidableEq State] [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s)
    {T : ℕ} (hT : 1 ≤ T) {f : (State → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {L₁ : ℝ}
    (hL₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ L₁) {L₂ : ℝ}
    (hL₂ : ∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ L₂ * ‖x - y‖) :
    |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * f (prGaussPart M π μ ω) -
        ∫ x, f x ∂(gaussCov (tdA M π μ) (trueGamma M π μ))| ≤
      L₂ * smoothLindebergConst M π μ μmin * (T : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hL2 : 0 ≤ L₂ := by
    obtain ⟨s⟩ := ‹Nonempty State›
    have h : 0 ≤ L₂ * ‖(Pi.single s (1 : ℝ) : State → ℝ) - 0‖ :=
      le_trans (by positivity) (hL₂ (Pi.single s 1) 0)
    have hpos : 0 < ‖(Pi.single s (1 : ℝ) : State → ℝ) - 0‖ := by
      rw [sub_zero, Pi.norm_single]; norm_num
    exact nonneg_of_mul_nonneg_left h hpos
  have hlin := lindeberg_iid (p := tupleProb M π μ) (tupleProb_nonneg M π μ) (sum_tupleProb M π μ)
    (sum_tupleProb_mul_tdY M π μ) (sum_tupleProb_mul_tdY_mul M π μ) hf hL₁ hL₂
    (lt_of_lt_of_le Nat.zero_lt_one hT)
  rw [← integral_gaussCov_eq M π μ hdiff.continuous.measurable] at hlin
  simp_rw [← prGaussPart_eq_smul_sum] at hlin
  have hm3 : ∑ x, tupleProb M π μ x * ‖tdY M π μ x‖ ^ 3 +
      ∫ z, ‖tdGaussFactor M π μ *ᵥ z‖ ^ 3 ∂(stdGaussianPi State) ≤
      6 * smoothLindebergConst M π μ μmin := by
    have h1 := sum_tupleProb_mul_norm_tdY_pow_three_le M π μ hμmin0 hμmin
    have h2 := integral_norm_tdGaussFactor_mulVec_pow_three_le M π μ hμmin0 hμmin
    simp only [smoothLindebergConst]
    linarith
  have hrpow : (T : ℝ) ^ (-(1 / 2 : ℝ)) = (√(T : ℝ))⁻¹ := by
    rw [Real.rpow_neg hT0.le, Real.sqrt_eq_rpow]
  calc _ ≤ L₂ / 6 * (∑ x, tupleProb M π μ x * ‖tdY M π μ x‖ ^ 3 +
        ∫ z, ‖tdGaussFactor M π μ *ᵥ z‖ ^ 3 ∂(stdGaussianPi State)) / √(T : ℝ) := by
        simpa [pathWeight] using hlin
    _ ≤ L₂ / 6 * (6 * smoothLindebergConst M π μ μmin) / √(T : ℝ) := by
        gcongr
    _ = L₂ * smoothLindebergConst M π μ μmin * (T : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [hrpow]; field_simp

/-! ## Main export -/

/-- **Smooth-test-function Gaussian approximation for Polyak–Ruppert-averaged TD
(Theorem 7.11 support). Partial result: not a restricted variant of Theorem 7.11 and
not counted in the named-result ledger.**

Setting as printed (`inference.tex:52–89`): i.i.d. tuples with weights `tupleProb`, step sizes
`η_t = η₀ t^{-2/3}`, `0 < η₀ ≤ 1` (the printed range `η₀ < 1/4` is included), any initial value
`V₀`, full-support `μ` (`0 < μmin ≤ μ(s)`, which makes `A⁻¹` genuine rather than Lean's junk `0`).
For every `T ≥ 1` and every `f : (State → ℝ) → ℝ` that is `C²` with `‖Df‖ ≤ L₁` and
`‖D²f(x) − D²f(y)‖ ≤ L₂‖x − y‖` (sup norm on `State → ℝ`, induced operator norms):
`|E f(√T Δ̄_T) − ∫ f d N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)| ≤ L₁ K T^{-1/6} + L₂ C T^{-1/2}` with
`K = smoothRemainderConst M π V₀ μmin η₀` and `C = smoothLindebergConst M π μ μmin`.

Differences from the printed Theorem 7.11 (`thm:Berry-Esseen-linear`, `inference.tex:132–141`):
1. metric: smooth test functions instead of the convex distance; it yields no set probabilities;
2. covariance: the true per-sample noise covariance `Γ_true` (`docs/SOURCE-ISSUES.md#C43`), not
   the printed `Γ` (with which the printed statement is refuted in Lean);
3. rate: `L₁ K T^{-1/6} + L₂ C T^{-1/2}` instead of a universal constant times the printed
   coefficient times `T^{-1/3}` plus `C̃ T^{-1/2}`. `T^{-1/6}` is the limit of this proof route
   (Gaussian approximation of the i.i.d. part `W_T` plus first-order control of `√TΔ̄_T − W_T`); it
   is not claimed to be the order of the distance itself (paper-level heuristics suggest
   `O(T^{-1/3})`; nothing about that, or about a lower bound, is proved here);
4. no `Γ ≻ 0` hypothesis (the Gaussian may be degenerate).

This result does **not** imply the printed Theorem 7.11, any convex-set or confidence-region
statement (`inference.tex:150–200`), or (in Lean) the classic CLT `eqn:classic-clt`. The constants
depend on the instance and, through `K`, on `V₀`; they are polynomial in `1/((1−γ) μmin η₀)` and
can be large, so the asymptotic regime may start late. `L₁` enters the `T^{-1/6}` term and also
guarantees integrability of `f` against the Gaussian (no junk Bochner value). -/
theorem scaledError_smooth_gaussian_le [DecidableEq State] [Nonempty State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    {μmin : ℝ} (hμmin0 : 0 < μmin) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ} (hT : 1 ≤ T)
    {f : (State → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {L₁ : ℝ} (hL₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ L₁)
    {L₂ : ℝ}
    (hL₂ : ∀ x y, ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ L₂ * ‖x - y‖) :
    |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * f (scaledError M π η₀ V₀ ω) -
        ∫ x, f x ∂(gaussCov (tdA M π μ) (trueGamma M π μ))| ≤
      L₁ * smoothRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 6 : ℝ)) +
        L₂ * smoothLindebergConst M π μ μmin * (T : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hL1 : 0 ≤ L₁ := (norm_nonneg _).trans (hL₁ 0)
  have hrem := abs_sum_mul_sub_sum_mul_le_weightedL2 (pathWeight_nonneg M π μ)
    (sum_pathWeight M π μ T) (fun a b ↦ abs_sub_le_of_norm_fderiv_le hdiff hL₁ b a) hL1
    (fun ω : Fin T → Tuple State Action ↦ scaledError M π η₀ V₀ ω)
    (fun ω ↦ prGaussPart M π μ ω)
  have hsum : ∑ s, weightedL2 (pathWeight M π μ) (fun ω : Fin T → Tuple State Action ↦
      scaledError M π η₀ V₀ ω s - prGaussPart M π μ ω s) ≤
      smoothRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 6 : ℝ)) := by
    calc _ ≤ ∑ _s : State, Fintype.card State * prRemainderConst M π V₀ μmin η₀ /
            ((1 - M.discount) * μmin) * (T : ℝ) ^ (-(1 / 6 : ℝ)) :=
          Finset.sum_le_sum fun s _ ↦
            weightedL2_scaledError_sub_prGaussPart_le_rpow M π μ h0 h1 V₀ hμmin0 hμmin hT s
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smoothRemainderConst]
          ring
  have hW := sum_pathWeight_mul_prGaussPart_smooth_le M π μ hμmin0 hμmin hT hf hL₁ hL₂
  calc _ = |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * f (scaledError M π η₀ V₀ ω) -
          ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * f (prGaussPart M π μ ω)) +
        (∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * f (prGaussPart M π μ ω) -
          ∫ x, f x ∂(gaussCov (tdA M π μ) (trueGamma M π μ)))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ L₁ * (smoothRemainderConst M π V₀ μmin η₀ * (T : ℝ) ^ (-(1 / 6 : ℝ))) +
        L₂ * smoothLindebergConst M π μ μmin * (T : ℝ) ^ (-(1 / 2 : ℝ)) :=
        add_le_add (hrem.trans (mul_le_mul_of_nonneg_left hsum hL1)) hW
    _ = _ := by ring

end StatisticalRL.Ch7Rest.TDInference

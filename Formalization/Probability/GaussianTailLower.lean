import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A lower bound on the standard Gaussian upper tail

`P(Z > 1) ≥ 0.15` for `Z ∼ N(0, 1)` (true value `0.15866`). Used by Example 6.1
(`chapters/offlineRL.tex:348–379`), whose proof states `P(r̄₂ ≥ 1) ≥ 0.15`.

Method: the tangent-line bound `e^u ≥ e^{u₀}(1 + u − u₀)` gives, for every `m` and `h ≥ 0`,
`∫_{m−h}^{m+h} e^{−x²/2} dx ≥ e^{−m²/2}(2h − h³/3)` (`integral_exp_neg_sq_half_ge`). Four
windows of width `1/2` with midpoints `5/4, 7/4, 9/4, 11/4` cover `[1, 3]`. The exponentials are
bounded with `Real.exp_bound'` (Taylor, eight terms) and `Real.exp_neg_one_gt_d9`, and
`√(2π) ≤ 2.5067` with `Real.pi_lt_d4`. The resulting bound is `≈ 0.1532`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatisticalRL.Probability

/-- Tangent-line lower bound for the Gaussian kernel at `m`, valid for every `x`. -/
theorem exp_neg_sq_half_ge_tangent (m x : ℝ) :
    exp (-m ^ 2 / 2) * (1 - (x ^ 2 - m ^ 2) / 2) ≤ exp (-x ^ 2 / 2) := by
  have h := add_one_le_exp (-(x ^ 2 - m ^ 2) / 2)
  have he : exp (-x ^ 2 / 2) = exp (-m ^ 2 / 2) * exp (-(x ^ 2 - m ^ 2) / 2) := by
    rw [← exp_add]; ring_nf
  rw [he]
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  linarith

/-- `∫_{m−h}^{m+h} e^{−x²/2} dx ≥ e^{−m²/2} (2h − h³/3)` for `h ≥ 0`. -/
theorem integral_exp_neg_sq_half_ge (m h : ℝ) (hh : 0 ≤ h) :
    exp (-m ^ 2 / 2) * (2 * h - h ^ 3 / 3) ≤ ∫ x in (m - h)..(m + h), exp (-x ^ 2 / 2) := by
  set C := exp (-m ^ 2 / 2)
  have hF : ∀ x ∈ Set.uIcc (m - h) (m + h),
      HasDerivAt (fun x ↦ C * (x - (x ^ 3 / 3 - m ^ 2 * x) / 2))
        (C * (1 - (x ^ 2 - m ^ 2) / 2)) x := by
    intro x _
    have h1 := hasDerivAt_id x
    have h3 := hasDerivAt_pow 3 x
    have := ((h1.sub (((h3.div_const 3).sub (h1.const_mul (m ^ 2))).div_const 2))).const_mul C
    convert this using 1
    simp
  have hint : ∫ x in (m - h)..(m + h), C * (1 - (x ^ 2 - m ^ 2) / 2) =
      C * (2 * h - h ^ 3 / 3) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (by
      apply Continuous.intervalIntegrable; fun_prop)]
    ring
  rw [← hint]
  refine intervalIntegral.integral_mono_on (by linarith)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop) fun x _ ↦ ?_
  exact exp_neg_sq_half_ge_tangent m x

private theorem exp_neg_le_of_exp_le {x U : ℝ} (h : exp x ≤ U) : U⁻¹ ≤ exp (-x) := by
  rw [exp_neg]
  exact inv_anti₀ (exp_pos x) h

/-- `e^{−25/32} ≥ 0.4578`. -/
theorem exp_neg_25_32_ge : (0.4578 : ℝ) ≤ exp (-(25 / 32)) := by
  have h := Real.exp_bound' (x := 25 / 32) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  refine le_trans ?_ (exp_neg_le_of_exp_le h)
  norm_num

/-- `e^{−17/32} ≥ 0.5878`. -/
theorem exp_neg_17_32_ge : (0.5878 : ℝ) ≤ exp (-(17 / 32)) := by
  have h := Real.exp_bound' (x := 17 / 32) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  refine le_trans ?_ (exp_neg_le_of_exp_le h)
  norm_num

/-- The four window midpoint values: `e^{−m²/2}` for `m = 5/4, 7/4, 9/4, 11/4`. -/
theorem four_window_sum_ge :
    (0.7762 : ℝ) ≤ exp (-(5 / 4) ^ 2 / 2) + exp (-(7 / 4) ^ 2 / 2) + exp (-(9 / 4) ^ 2 / 2) +
      exp (-(11 / 4) ^ 2 / 2) := by
  have hA := exp_neg_25_32_ge
  have hB := exp_neg_17_32_ge
  have he := Real.exp_neg_one_gt_d9
  have e1 : exp (-(5 / 4 : ℝ) ^ 2 / 2) = exp (-(25 / 32)) := by norm_num
  have e2 : exp (-(7 / 4 : ℝ) ^ 2 / 2) = exp (-1) * exp (-(17 / 32)) := by
    rw [← exp_add]; norm_num
  have e3 : exp (-(9 / 4 : ℝ) ^ 2 / 2) = exp (-1) * exp (-1) * exp (-(17 / 32)) := by
    rw [← exp_add, ← exp_add]; norm_num
  have e4 : exp (-(11 / 4 : ℝ) ^ 2 / 2) = exp (-1) * exp (-1) * exp (-1) * exp (-(25 / 32)) := by
    rw [← exp_add, ← exp_add, ← exp_add]; norm_num
  rw [e1, e2, e3, e4]
  have hpos : (0 : ℝ) ≤ 0.36787944116 := by norm_num
  have h1 : (0.36787944116 : ℝ) * 0.5878 ≤ exp (-1) * exp (-(17 / 32)) :=
    mul_le_mul he.le hB (by norm_num) (exp_pos _).le
  have h2 : (0.36787944116 : ℝ) * 0.36787944116 ≤ exp (-1) * exp (-1) :=
    mul_le_mul he.le he.le hpos (exp_pos _).le
  have h3 : (0.36787944116 : ℝ) * 0.36787944116 * 0.5878 ≤
      exp (-1) * exp (-1) * exp (-(17 / 32)) :=
    mul_le_mul h2 hB (by norm_num) (by positivity)
  have h4 : (0.36787944116 : ℝ) * 0.36787944116 * 0.36787944116 ≤
      exp (-1) * exp (-1) * exp (-1) :=
    mul_le_mul h2 he.le hpos (by positivity)
  have h5 : (0.36787944116 : ℝ) * 0.36787944116 * 0.36787944116 * 0.4578 ≤
      exp (-1) * exp (-1) * exp (-1) * exp (-(25 / 32)) :=
    mul_le_mul h4 hA (by norm_num) (by positivity)
  nlinarith [h1, h3, h5, hA]

/-- `∫_1^3 e^{−x²/2} dx ≥ (95/192) · 0.7762`. -/
theorem integral_one_three_exp_neg_sq_half_ge :
    (95 / 192 : ℝ) * 0.7762 ≤ ∫ x in (1 : ℝ)..3, exp (-x ^ 2 / 2) := by
  have hc : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ ↦ exp (-x ^ 2 / 2)) volume a b := by
    intro a b; apply Continuous.intervalIntegrable; fun_prop
  have w1 := integral_exp_neg_sq_half_ge (5 / 4) (1 / 4) (by norm_num)
  have w2 := integral_exp_neg_sq_half_ge (7 / 4) (1 / 4) (by norm_num)
  have w3 := integral_exp_neg_sq_half_ge (9 / 4) (1 / 4) (by norm_num)
  have w4 := integral_exp_neg_sq_half_ge (11 / 4) (1 / 4) (by norm_num)
  norm_num at w1 w2 w3 w4
  have hsum := four_window_sum_ge
  norm_num at hsum
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc 1 2) (hc 2 3),
    ← intervalIntegral.integral_add_adjacent_intervals (hc 1 (3 / 2)) (hc (3 / 2) 2),
    ← intervalIntegral.integral_add_adjacent_intervals (hc 2 (5 / 2)) (hc (5 / 2) 3)]
  norm_num
  linarith

end StatisticalRL.Probability

namespace StatisticalRL.Probability

/-- **Standard Gaussian tail lower bound**: `P(Z > 1) ≥ 0.15` for `Z ∼ N(0,1)` (real form). -/
theorem gaussianReal_Ioi_one_ge_real : (0.15 : ℝ) ≤ ∫ x in Set.Ioi (1 : ℝ), gaussianPDFReal 0 1 x := by
  have hsq : √(2 * π * ((1 : ℝ≥0) : ℝ)) ≤ 2.5067 := by
    rw [show (2.5067 : ℝ) = √(2.5067 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by push_cast; nlinarith [Real.pi_lt_d4])
  have hsqpos : 0 < √(2 * π * ((1 : ℝ≥0) : ℝ)) := Real.sqrt_pos.2 (by push_cast; positivity)
  have hmono : ∫ x in Set.Ioc (1 : ℝ) 3, gaussianPDFReal 0 1 x ≤
      ∫ x in Set.Ioi (1 : ℝ), gaussianPDFReal 0 1 x :=
    setIntegral_mono_set (integrable_gaussianPDFReal 0 1).integrableOn
      (ae_of_all _ (gaussianPDFReal_nonneg 0 1)) Set.Ioc_subset_Ioi_self.eventuallyLE
  refine le_trans ?_ hmono
  rw [← intervalIntegral.integral_of_le (by norm_num)]
  have hfun : (fun x ↦ gaussianPDFReal 0 1 x) =
      fun x ↦ (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ * exp (-x ^ 2 / 2) := by
    funext x; simp [gaussianPDFReal]
  rw [hfun, intervalIntegral.integral_const_mul]
  have hI := integral_one_three_exp_neg_sq_half_ge
  have hinv : (2.5067 : ℝ)⁻¹ ≤ (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ := inv_anti₀ hsqpos hsq
  have hIpos : (0 : ℝ) ≤ 95 / 192 * 0.7762 := by norm_num
  calc (0.15 : ℝ) ≤ (2.5067 : ℝ)⁻¹ * (95 / 192 * 0.7762) := by norm_num
    _ ≤ (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ * ∫ x in (1 : ℝ)..3, exp (-x ^ 2 / 2) :=
      mul_le_mul hinv hI hIpos (inv_nonneg.2 hsqpos.le)

/-- **Standard Gaussian tail lower bound**: `N(0,1)((1, ∞)) ≥ 0.15`. -/
theorem gaussianReal_Ioi_one_ge : ENNReal.ofReal 0.15 ≤ gaussianReal 0 1 (Set.Ioi 1) := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  exact ENNReal.ofReal_le_ofReal gaussianReal_Ioi_one_ge_real

end StatisticalRL.Probability

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The normal Stein equation for half-line indicators

Standard normal density `stdPDF`, distribution function `stdCDF` and tail `stdTail`, the two
Mills-ratio inequalities, and the solution `steinSol z` of the Stein equation

`f'(w) - w f(w) = 1{w ≤ z} - Φ(z)`

with explicit (crude) bounds `|w f(w)| ≤ 1`, `0 ≤ f ≤ 5`, `|f'| ≤ 2`. The derivative
`steinDeriv z w = w f(w) + 1{w ≤ z} - Φ(z)` is discontinuous at `z`; the fundamental theorem of
calculus `steinSol_sub_eq_integral` is proved with the countable-exception version
`MeasureTheory.integral_eq_of_hasDerivAt_off_countable`.

The clipped ramp `ramp a b δ` used in the concentration inequality is also defined here.
No probability space enters this file.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace StatisticalRL.Probability.Stein

/-! ## Standard normal density, distribution function and tail -/

/-- The standard normal density `φ(x) = (2π)^{-1/2} e^{-x²/2}`. -/
noncomputable def stdPDF (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- The standard normal distribution function `Φ(z) = ∫_{-∞}^z φ`. -/
noncomputable def stdCDF (z : ℝ) : ℝ := ∫ x in Iic z, stdPDF x

/-- The standard normal tail `1 - Φ(z) = ∫_z^∞ φ`. -/
noncomputable def stdTail (z : ℝ) : ℝ := ∫ x in Ioi z, stdPDF x

theorem stdPDF_eq (x : ℝ) : stdPDF x = (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := by
  simp [stdPDF, gaussianPDFReal]

theorem stdPDF_pos (x : ℝ) : 0 < stdPDF x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

theorem stdPDF_neg (x : ℝ) : stdPDF (-x) = stdPDF x := by
  simp [stdPDF_eq]

theorem continuous_stdPDF : Continuous stdPDF := by
  have : stdPDF = fun x ↦ (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := funext stdPDF_eq
  rw [this]
  fun_prop

theorem integrable_stdPDF : Integrable stdPDF := integrable_gaussianPDFReal 0 1

theorem hasDerivAt_stdPDF (x : ℝ) : HasDerivAt stdPDF (-x * stdPDF x) x := by
  have : stdPDF = fun x ↦ (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := funext stdPDF_eq
  rw [this]
  have h1 : HasDerivAt (fun x : ℝ ↦ -x ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert this using 1
    push_cast
    ring
  have h2 := (h1.exp).const_mul (√(2 * π))⁻¹
  convert h2 using 1
  ring

theorem tendsto_stdPDF_atTop : Tendsto stdPDF atTop (𝓝 0) := by
  have : stdPDF = fun x ↦ (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := funext stdPDF_eq
  rw [this]
  have h : Tendsto (fun x : ℝ ↦ exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_comp_nhds_zero.mpr
    have : Tendsto (fun x : ℝ ↦ x ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
    have := tendsto_neg_atTop_atBot.comp this
    refine this.congr fun x ↦ ?_
    simp only [Function.comp]
    ring
  simpa using h.const_mul (√(2 * π))⁻¹

theorem stdCDF_nonneg (z : ℝ) : 0 ≤ stdCDF z :=
  setIntegral_nonneg measurableSet_Iic fun x _ ↦ (stdPDF_pos x).le

theorem stdTail_nonneg (z : ℝ) : 0 ≤ stdTail z :=
  setIntegral_nonneg measurableSet_Ioi fun x _ ↦ (stdPDF_pos x).le

theorem stdCDF_add_stdTail (z : ℝ) : stdCDF z + stdTail z = 1 := by
  have h := setIntegral_union (μ := volume) (f := stdPDF) (Iic_disjoint_Ioi (le_refl z))
    measurableSet_Ioi integrable_stdPDF.integrableOn integrable_stdPDF.integrableOn
  rw [Iic_union_Ioi, setIntegral_univ] at h
  rw [stdCDF, stdTail, ← h]
  exact integral_gaussianPDFReal_eq_one 0 one_ne_zero

theorem stdTail_eq (z : ℝ) : stdTail z = 1 - stdCDF z := by
  linarith [stdCDF_add_stdTail z]

theorem stdCDF_le_one (z : ℝ) : stdCDF z ≤ 1 := by
  linarith [stdCDF_add_stdTail z, stdTail_nonneg z]

theorem stdTail_le_one (z : ℝ) : stdTail z ≤ 1 := by
  linarith [stdCDF_add_stdTail z, stdCDF_nonneg z]

theorem stdCDF_mono {a b : ℝ} (hab : a ≤ b) : stdCDF a ≤ stdCDF b :=
  setIntegral_mono_set integrable_stdPDF.integrableOn
    (ae_of_all _ fun x ↦ (stdPDF_pos x).le) (Eventually.of_forall (Iic_subset_Iic.2 hab))

theorem stdTail_anti {a b : ℝ} (hab : a ≤ b) : stdTail b ≤ stdTail a := by
  rw [stdTail_eq, stdTail_eq]
  linarith [stdCDF_mono hab]

/-- `Φ(w) = 1 - Φ(-w)`, in the form `Φ(w) = Q(-w)`. -/
theorem stdCDF_eq_stdTail_neg (w : ℝ) : stdCDF w = stdTail (-w) := by
  rw [stdCDF, stdTail, ← integral_comp_neg_Iic]
  simp only [stdPDF_neg]

/-- The link with Mathlib's Gaussian measure. -/
theorem gaussianReal_real_Iic (z : ℝ) : (gaussianReal 0 1).real (Iic z) = stdCDF z := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
      fun x _ ↦ gaussianPDFReal_nonneg 0 1 x)]
  rfl

theorem hasDerivAt_stdCDF (z : ℝ) : HasDerivAt stdCDF (stdPDF z) z := by
  have h : stdCDF = fun u ↦ stdCDF 0 + ∫ x in (0 : ℝ)..u, stdPDF x := by
    funext u
    rw [stdCDF, stdCDF, ← intervalIntegral.integral_Iic_sub_Iic integrable_stdPDF.integrableOn
      integrable_stdPDF.integrableOn]
    ring
  rw [h]
  exact ((continuous_stdPDF.integral_hasStrictDerivAt 0 z).hasDerivAt).const_add _

theorem continuous_stdCDF : Continuous stdCDF :=
  continuous_iff_continuousAt.2 fun z ↦ (hasDerivAt_stdCDF z).continuousAt

theorem hasDerivAt_stdTail (z : ℝ) : HasDerivAt stdTail (-stdPDF z) z := by
  have h : stdTail = fun u ↦ 1 - stdCDF u := funext stdTail_eq
  rw [h]
  exact (hasDerivAt_stdCDF z).const_sub 1

theorem continuous_stdTail : Continuous stdTail :=
  continuous_iff_continuousAt.2 fun z ↦ (hasDerivAt_stdTail z).continuousAt

/-! ## Mills ratio -/

theorem integrableOn_Ioi_mul_stdPDF (w : ℝ) (hw : 0 ≤ w) :
    IntegrableOn (fun t ↦ t * stdPDF t) (Ioi w) := by
  have hd : ∀ x ∈ Ioi w, HasDerivAt (fun t ↦ -stdPDF t) (x * stdPDF x) x := fun x _ ↦ by
    have := (hasDerivAt_stdPDF x).neg
    convert this using 1
    ring
  have hlim : Tendsto (fun t ↦ -stdPDF t) atTop (𝓝 0) := by
    simpa using tendsto_stdPDF_atTop.neg
  exact integrableOn_Ioi_deriv_of_nonneg continuous_stdPDF.neg.continuousWithinAt hd
    (fun x hx ↦ mul_nonneg (hw.trans (le_of_lt (mem_Ioi.1 hx))) (stdPDF_pos x).le) hlim

/-- `∫_w^∞ t φ(t) dt = φ(w)`. -/
theorem integral_Ioi_mul_stdPDF (w : ℝ) (hw : 0 ≤ w) : ∫ t in Ioi w, t * stdPDF t = stdPDF w := by
  have hd : ∀ x ∈ Ioi w, HasDerivAt (fun t ↦ -stdPDF t) (x * stdPDF x) x := fun x _ ↦ by
    have := (hasDerivAt_stdPDF x).neg
    convert this using 1
    ring
  have hlim : Tendsto (fun t ↦ -stdPDF t) atTop (𝓝 0) := by
    simpa using tendsto_stdPDF_atTop.neg
  have hc : ContinuousWithinAt (fun t ↦ -stdPDF t) (Ici w) w :=
    continuous_stdPDF.neg.continuousWithinAt
  have := integral_Ioi_of_hasDerivAt_of_tendsto hc hd ?_ hlim
  · rw [this]
    ring
  · exact integrableOn_Ioi_mul_stdPDF w hw

/-- **Mills ratio, upper tail.** For `w ≥ 0`, `w (1 - Φ(w)) ≤ φ(w)`. -/
theorem mul_stdTail_le (w : ℝ) (hw : 0 ≤ w) : w * stdTail w ≤ stdPDF w := by
  rw [stdTail, ← integral_const_mul, ← integral_Ioi_mul_stdPDF w hw]
  refine setIntegral_mono_on (integrable_stdPDF.integrableOn.const_mul w)
    (integrableOn_Ioi_mul_stdPDF w hw) measurableSet_Ioi fun t ht ↦ ?_
  exact mul_le_mul_of_nonneg_right (le_of_lt (mem_Ioi.1 ht)) (stdPDF_pos t).le

/-- **Mills ratio, lower tail.** For `w ≤ 0`, `-w Φ(w) ≤ φ(w)`. -/
theorem neg_mul_stdCDF_le (w : ℝ) (hw : w ≤ 0) : -w * stdCDF w ≤ stdPDF w := by
  rw [stdCDF_eq_stdTail_neg, ← stdPDF_neg]
  exact mul_stdTail_le (-w) (by linarith)

/-- `φ(w) ≥ 1/5` for `|w| ≤ 1`. -/
theorem stdPDF_ge_fifth {w : ℝ} (hw : |w| ≤ 1) : 1 / 5 ≤ stdPDF w := by
  rw [stdPDF_eq]
  have hw2 : w ^ 2 ≤ 1 := by
    have := sq_abs w
    nlinarith [abs_nonneg w]
  have he : exp (-1 / 2) ≤ exp (-w ^ 2 / 2) := exp_le_exp.2 (by linarith)
  have hpi : π < 3.15 := pi_lt_d2
  have hpi0 : 0 < π := pi_pos
  have hs : √(2 * π) ≤ 2.51 := by
    rw [sqrt_le_left (by norm_num)]
    nlinarith
  have hspos : 0 < √(2 * π) := sqrt_pos.2 (by positivity)
  have he1 : exp (1 / 2) ≤ 1.65 := by
    have h := exp_one_lt_d9
    have hsq : exp (1 / 2) ^ 2 = exp 1 := by rw [← exp_nat_mul]; norm_num
    nlinarith [exp_pos (1 / 2)]
  have he2 : exp (-1 / 2) = (exp (1 / 2))⁻¹ := by rw [← exp_neg]; norm_num
  rw [he2] at he
  have hep : 0 < exp (1 / 2) := exp_pos _
  calc (1 : ℝ) / 5 ≤ (√(2 * π))⁻¹ * (exp (1 / 2))⁻¹ := by
        rw [← mul_inv]
        rw [div_le_iff₀ (by norm_num), ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
        nlinarith
    _ ≤ (√(2 * π))⁻¹ * exp (-w ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left he (inv_nonneg.2 hspos.le)

/-! ## The Stein solution for `1{w ≤ z}` -/

/-- The half-line indicator `1{w ≤ z}`. -/
noncomputable def steinInd (z w : ℝ) : ℝ := if w ≤ z then 1 else 0

/-- The indicator `1{a ≤ v ≤ b}` of a closed interval. -/
noncomputable def intervalInd (a b v : ℝ) : ℝ := if a ≤ v ∧ v ≤ b then 1 else 0

/-- Numerator of the Stein solution: `(1-Φ(z))Φ(w)` for `w ≤ z`, `Φ(z)(1-Φ(w))` for `w > z`. -/
noncomputable def steinNum (z w : ℝ) : ℝ :=
  if w ≤ z then stdTail z * stdCDF w else stdCDF z * stdTail w

/-- The bounded solution `f_z = steinNum z / φ` of the Stein equation
`f'(w) - w f(w) = 1{w ≤ z} - Φ(z)`. -/
noncomputable def steinSol (z w : ℝ) : ℝ := steinNum z w / stdPDF w

/-- The derivative of `steinSol z` off `z`: `w f_z(w) + 1{w ≤ z} - Φ(z)`. -/
noncomputable def steinDeriv (z w : ℝ) : ℝ := w * steinSol z w + steinInd z w - stdCDF z

theorem steinInd_nonneg (z w : ℝ) : 0 ≤ steinInd z w := by
  unfold steinInd; split_ifs <;> norm_num

theorem steinInd_le_one (z w : ℝ) : steinInd z w ≤ 1 := by
  unfold steinInd; split_ifs <;> norm_num

theorem intervalInd_nonneg (a b v : ℝ) : 0 ≤ intervalInd a b v := by
  unfold intervalInd; split_ifs <;> norm_num

theorem intervalInd_le_one (a b v : ℝ) : intervalInd a b v ≤ 1 := by
  unfold intervalInd; split_ifs <;> norm_num

theorem steinNum_nonneg (z w : ℝ) : 0 ≤ steinNum z w := by
  unfold steinNum
  split_ifs
  · exact mul_nonneg (stdTail_nonneg z) (stdCDF_nonneg w)
  · exact mul_nonneg (stdCDF_nonneg z) (stdTail_nonneg w)

theorem steinNum_le_one (z w : ℝ) : steinNum z w ≤ 1 := by
  unfold steinNum
  split_ifs
  · exact mul_le_one₀ (stdTail_le_one z) (stdCDF_nonneg w) (stdCDF_le_one w)
  · exact mul_le_one₀ (stdCDF_le_one z) (stdTail_nonneg w) (stdTail_le_one w)

/-- The Mills-ratio estimate behind `|w f_z(w)| ≤ 1`. -/
theorem abs_mul_steinNum_le (z w : ℝ) : |w| * steinNum z w ≤ stdPDF w := by
  unfold steinNum
  split_ifs with h
  · rcases le_total 0 w with hw | hw
    · rw [abs_of_nonneg hw]
      calc w * (stdTail z * stdCDF w) ≤ w * (stdTail w * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (stdTail_anti h) (stdCDF_le_one w)
              (stdCDF_nonneg w) (stdTail_nonneg w)) hw
        _ = w * stdTail w := by ring
        _ ≤ stdPDF w := mul_stdTail_le w hw
    · rw [abs_of_nonpos hw]
      calc -w * (stdTail z * stdCDF w) ≤ -w * (1 * stdCDF w) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (stdTail_le_one z)
              (stdCDF_nonneg w)) (by linarith)
        _ = -w * stdCDF w := by ring
        _ ≤ stdPDF w := neg_mul_stdCDF_le w hw
  · push_neg at h
    rcases le_total 0 w with hw | hw
    · rw [abs_of_nonneg hw]
      calc w * (stdCDF z * stdTail w) ≤ w * (1 * stdTail w) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (stdCDF_le_one z)
              (stdTail_nonneg w)) hw
        _ = w * stdTail w := by ring
        _ ≤ stdPDF w := mul_stdTail_le w hw
    · rw [abs_of_nonpos hw]
      calc -w * (stdCDF z * stdTail w) ≤ -w * (stdCDF w * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (stdCDF_mono h.le) (stdTail_le_one w)
              (stdTail_nonneg w) (stdCDF_nonneg w)) (by linarith)
        _ = -w * stdCDF w := by ring
        _ ≤ stdPDF w := neg_mul_stdCDF_le w hw

theorem steinSol_nonneg (z w : ℝ) : 0 ≤ steinSol z w :=
  div_nonneg (steinNum_nonneg z w) (stdPDF_pos w).le

/-- `|w f_z(w)| ≤ 1`. -/
theorem abs_mul_steinSol_le_one (z w : ℝ) : |w * steinSol z w| ≤ 1 := by
  rw [steinSol, abs_mul, abs_of_nonneg (div_nonneg (steinNum_nonneg z w) (stdPDF_pos w).le),
    ← mul_div_assoc, div_le_one (stdPDF_pos w)]
  exact abs_mul_steinNum_le z w

/-- `f_z ≤ 5` (crude; the sharp bound is `√(2π)/4`). -/
theorem steinSol_le_five (z w : ℝ) : steinSol z w ≤ 5 := by
  rcases le_or_gt 1 |w| with hw | hw
  · have h1 := abs_mul_steinSol_le_one z w
    rw [abs_mul, abs_of_nonneg (steinSol_nonneg z w)] at h1
    nlinarith [steinSol_nonneg z w]
  · have hφ := stdPDF_ge_fifth hw.le
    have hpos := stdPDF_pos w
    rw [steinSol, div_le_iff₀ hpos]
    nlinarith [steinNum_le_one z w]

theorem abs_steinSol_le_five (z w : ℝ) : |steinSol z w| ≤ 5 := by
  rw [abs_of_nonneg (steinSol_nonneg z w)]
  exact steinSol_le_five z w

/-- `|f_z'| ≤ 2` (crude; the sharp bound is `1`). -/
theorem abs_steinDeriv_le_two (z w : ℝ) : |steinDeriv z w| ≤ 2 := by
  have h1 := abs_mul_steinSol_le_one z w
  have h2 : |steinInd z w - stdCDF z| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [steinInd_nonneg z w, steinInd_le_one z w, stdCDF_nonneg z,
      stdCDF_le_one z]
  calc |steinDeriv z w| = |w * steinSol z w + (steinInd z w - stdCDF z)| := by
        rw [steinDeriv]; ring_nf
    _ ≤ |w * steinSol z w| + |steinInd z w - stdCDF z| := abs_add_le _ _
    _ ≤ 2 := by linarith

theorem continuous_steinNum (z : ℝ) : Continuous (steinNum z) := by
  have : steinNum z = fun w ↦ if w ≤ z then stdTail z * stdCDF w else stdCDF z * stdTail w := rfl
  rw [this]
  refine Continuous.if_le (continuous_const.mul continuous_stdCDF)
    (continuous_const.mul continuous_stdTail) continuous_id continuous_const fun x hx ↦ ?_
  rw [show x = z from hx]
  ring

theorem continuous_steinSol (z : ℝ) : Continuous (steinSol z) :=
  (continuous_steinNum z).div continuous_stdPDF fun w ↦ (stdPDF_pos w).ne'

theorem hasDerivAt_steinSol {z w : ℝ} (hw : w ≠ z) :
    HasDerivAt (steinSol z) (steinDeriv z w) w := by
  have hφ := hasDerivAt_stdPDF w
  have hpos := stdPDF_pos w
  rcases lt_or_gt_of_ne hw with h | h
  · have hN : HasDerivAt (steinNum z) (stdTail z * stdPDF w) w := by
      have h0 := (hasDerivAt_stdCDF w).const_mul (stdTail z)
      refine h0.congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with v hv
      simp [steinNum, le_of_lt (mem_Iio.1 hv)]
    have := hN.div hφ hpos.ne'
    convert this using 1
    simp only [steinDeriv, steinSol, steinInd, steinNum, le_of_lt h, if_true, stdTail_eq]
    field_simp
    ring
  · have hN : HasDerivAt (steinNum z) (stdCDF z * -stdPDF w) w := by
      have h0 := (hasDerivAt_stdTail w).const_mul (stdCDF z)
      refine h0.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h] with v hv
      simp [steinNum, not_le.2 (mem_Ioi.1 hv)]
    have := hN.div hφ hpos.ne'
    convert this using 1
    simp only [steinDeriv, steinSol, steinInd, steinNum, not_le.2 h, if_false]
    field_simp
    ring

theorem antitone_steinInd (z : ℝ) : Antitone (steinInd z) := by
  intro a b hab
  unfold steinInd
  split_ifs with h1 h2 <;> norm_num
  linarith

theorem intervalIntegrable_steinDeriv_comp (z v a b : ℝ) :
    IntervalIntegrable (fun t ↦ steinDeriv z (v + t)) volume a b := by
  have hc : Continuous fun t ↦ (v + t) * steinSol z (v + t) :=
    (continuous_const.add continuous_id).mul
      ((continuous_steinSol z).comp (continuous_const.add continuous_id))
  have ha : Antitone fun t ↦ steinInd z (v + t) := fun x y hxy ↦
    antitone_steinInd z (by linarith : v + x ≤ v + y)
  have := ((hc.intervalIntegrable a b).add (ha.intervalIntegrable (a := a) (b := b))).sub
    (intervalIntegrable_const : IntervalIntegrable (fun _ ↦ stdCDF z) volume a b)
  exact this

theorem intervalIntegrable_steinDeriv (z a b : ℝ) :
    IntervalIntegrable (steinDeriv z) volume a b := by
  simpa using intervalIntegrable_steinDeriv_comp z 0 a b

/-- **Fundamental theorem of calculus for the Stein solution** (derivative off `{z}`). -/
theorem steinSol_sub_eq_integral (z a b : ℝ) :
    ∫ t in a..b, steinDeriv z t = steinSol z b - steinSol z a :=
  integral_eq_of_hasDerivAt_off_countable _ _ (countable_singleton z)
    (continuous_steinSol z).continuousOn
    (fun _ hx ↦ hasDerivAt_steinSol fun h ↦ hx.2 (mem_singleton_iff.2 h))
    (intervalIntegrable_steinDeriv z a b)

/-- Shifted form: `f_z(v + u) - f_z(v) = ∫₀ᵘ f_z'(v + t) dt`. -/
theorem steinSol_add_sub_eq_integral (z v u : ℝ) :
    steinSol z (v + u) - steinSol z v = ∫ t in (0 : ℝ)..u, steinDeriv z (v + t) := by
  rw [intervalIntegral.integral_comp_add_left (steinDeriv z) v, add_zero,
    steinSol_sub_eq_integral]

/-- `f_z` is `2`-Lipschitz. -/
theorem abs_steinSol_sub_le (z a b : ℝ) : |steinSol z b - steinSol z a| ≤ 2 * |b - a| := by
  rw [← steinSol_sub_eq_integral]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (f := steinDeriv z) (a := a) (b := b)
    (C := 2) fun x _ ↦ by rw [Real.norm_eq_abs]; exact abs_steinDeriv_le_two z x
  rwa [Real.norm_eq_abs] at this

/-- `|(v+u) f(v+u) - (v+t) f(v+t)| ≤ (2|v| + 5)(|u| + |t|)`. -/
theorem abs_mul_steinSol_sub_le (z v u t : ℝ) :
    |(v + u) * steinSol z (v + u) - (v + t) * steinSol z (v + t)| ≤
      (2 * |v| + 5) * (|u| + |t|) := by
  have h1 := abs_steinSol_sub_le z (v + t) (v + u)
  have h2 := abs_steinSol_le_five z (v + u)
  have h3 := abs_steinSol_le_five z (v + t)
  have hut : |v + u - (v + t)| ≤ |u| + |t| := by
    rw [show v + u - (v + t) = u + -t by ring]
    exact (abs_add_le _ _).trans (by rw [abs_neg])
  calc |(v + u) * steinSol z (v + u) - (v + t) * steinSol z (v + t)|
        = |v * (steinSol z (v + u) - steinSol z (v + t)) + u * steinSol z (v + u) +
            -(t * steinSol z (v + t))| := by ring_nf
    _ ≤ |v * (steinSol z (v + u) - steinSol z (v + t))| + |u * steinSol z (v + u)| +
          |-(t * steinSol z (v + t))| := abs_add_three _ _ _
    _ = |v| * |steinSol z (v + u) - steinSol z (v + t)| + |u| * |steinSol z (v + u)| +
          |t| * |steinSol z (v + t)| := by rw [abs_neg, abs_mul, abs_mul, abs_mul]
    _ ≤ |v| * (2 * (|u| + |t|)) + |u| * 5 + |t| * 5 := by
        gcongr
        exact h1.trans (by gcongr)
    _ = (2 * |v| + 5) * (|u| + |t|) := by ring

theorem abs_steinInd_sub_le (z v u t : ℝ) :
    |steinInd z (v + u) - steinInd z (v + t)| ≤ intervalInd (z - max u t) (z - min u t) v := by
  have h1 := le_max_left u t
  have h2 := le_max_right u t
  have h3 := min_le_left u t
  have h4 := min_le_right u t
  by_cases hu : v + u ≤ z <;> by_cases ht : v + t ≤ z
  · simp only [steinInd, hu, ht, if_true, sub_self, abs_zero]
    exact intervalInd_nonneg _ _ _
  · have hin : z - max u t ≤ v ∧ v ≤ z - min u t := ⟨by linarith, by linarith⟩
    simp [steinInd, intervalInd, hu, ht, hin]
  · have hin : z - max u t ≤ v ∧ v ≤ z - min u t := ⟨by linarith, by linarith⟩
    simp [steinInd, intervalInd, hu, ht, hin]
  · simp only [steinInd, hu, ht, if_false, sub_self, abs_zero]
    exact intervalInd_nonneg _ _ _

/-- The basic increment estimate for `f_z'`:
`|f_z'(v+u) - f_z'(v+t)| ≤ (2|v|+5)(|u|+|t|) + 1{z - max(u,t) ≤ v ≤ z - min(u,t)}`. -/
theorem abs_steinDeriv_sub_le (z v u t : ℝ) :
    |steinDeriv z (v + u) - steinDeriv z (v + t)| ≤
      (2 * |v| + 5) * (|u| + |t|) + intervalInd (z - max u t) (z - min u t) v := by
  have h := abs_add_le ((v + u) * steinSol z (v + u) - (v + t) * steinSol z (v + t))
    (steinInd z (v + u) - steinInd z (v + t))
  calc |steinDeriv z (v + u) - steinDeriv z (v + t)|
        = |((v + u) * steinSol z (v + u) - (v + t) * steinSol z (v + t)) +
            (steinInd z (v + u) - steinInd z (v + t))| := by
          simp only [steinDeriv]; ring_nf
    _ ≤ _ := h
    _ ≤ _ := add_le_add (abs_mul_steinSol_sub_le z v u t) (abs_steinInd_sub_le z v u t)

/-! ## The clipped ramp of the concentration inequality -/

/-- The ramp `w ↦ w - (a+b)/2` clipped to `[-((b-a)/2+δ), (b-a)/2+δ]`. -/
noncomputable def ramp (a b δ w : ℝ) : ℝ :=
  max (-((b - a) / 2 + δ)) (min (w - (a + b) / 2) ((b - a) / 2 + δ))

theorem ramp_mono (a b δ : ℝ) : Monotone (ramp a b δ) := fun x y hxy ↦
  max_le_max le_rfl (min_le_min (by linarith) le_rfl)

theorem abs_ramp_le {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 ≤ δ) (w : ℝ) :
    |ramp a b δ w| ≤ (b - a) / 2 + δ := by
  unfold ramp
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem ramp_eq {a b δ w : ℝ} (h1 : a - δ ≤ w) (h2 : w ≤ b + δ) :
    ramp a b δ w = w - (a + b) / 2 := by
  unfold ramp
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]

theorem mul_ramp_sub_nonneg (a b δ W x : ℝ) : 0 ≤ x * (ramp a b δ W - ramp a b δ (W - x)) := by
  rcases le_total 0 x with hx | hx
  · exact mul_nonneg hx (sub_nonneg.2 (ramp_mono a b δ (by linarith)))
  · exact mul_nonneg_of_nonpos_of_nonpos hx (sub_nonpos.2 (ramp_mono a b δ (by linarith)))

/-- On `{a ≤ W ≤ b}`: `|x| min(δ,|x|) ≤ x (g(W) - g(W - x))` for the ramp `g`. -/
theorem abs_mul_min_le_mul_ramp_sub {a b δ W : ℝ} (hδ : 0 < δ) (haW : a ≤ W) (hWb : W ≤ b)
    (x : ℝ) : |x| * min δ |x| ≤ x * (ramp a b δ W - ramp a b δ (W - x)) := by
  have hW : ramp a b δ W = W - (a + b) / 2 := ramp_eq (by linarith) (by linarith)
  rcases le_or_gt |x| δ with hx | hx
  · rw [min_eq_right hx]
    have hx' := abs_le.1 hx
    rw [hW, ramp_eq (by linarith) (by linarith)]
    have : |x| * |x| = x * x := by rw [← abs_mul, abs_mul_self]
    rw [this]; ring_nf; exact le_rfl
  · rw [min_eq_left hx.le]
    rcases le_total 0 x with h0 | h0
    · rw [abs_of_nonneg h0] at hx ⊢
      have hm : ramp a b δ (W - x) ≤ ramp a b δ (W - δ) := ramp_mono a b δ (by linarith)
      rw [ramp_eq (w := W - δ) (by linarith) (by linarith)] at hm
      rw [hW]
      nlinarith
    · rw [abs_of_nonpos h0] at hx ⊢
      have hm : ramp a b δ (W + δ) ≤ ramp a b δ (W - x) := ramp_mono a b δ (by linarith)
      rw [ramp_eq (w := W + δ) (by linarith) (by linarith)] at hm
      rw [hW]
      nlinarith

theorem sq_sub_le_abs_mul_min {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    x ^ 2 - |x| ^ 3 / (4 * δ) ≤ |x| * min δ |x| := by
  have hx3 : 0 ≤ |x| ^ 3 / (4 * δ) := by positivity
  have hsq : x ^ 2 = |x| * |x| := by rw [← abs_mul, ← sq, abs_sq]
  rcases le_total |x| δ with h | h
  · rw [min_eq_right h, hsq]; linarith
  · rw [min_eq_left h, hsq]
    have ha := abs_nonneg x
    have key : (|x| * |x| - |x| * δ) * (4 * δ) ≤ |x| ^ 3 := by
      nlinarith [mul_nonneg ha (sq_nonneg (|x| - 2 * δ))]
    have : |x| * |x| - |x| * δ ≤ |x| ^ 3 / (4 * δ) := by
      rw [le_div_iff₀ (by positivity)]; exact key
    linarith

theorem abs_mul_min_nonneg (δ : ℝ) (hδ : 0 ≤ δ) (x : ℝ) : 0 ≤ |x| * min δ |x| :=
  mul_nonneg (abs_nonneg x) (le_min hδ (abs_nonneg x))

theorem sq_abs_mul_min_le {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) : (|x| * min δ |x|) ^ 2 ≤ δ ^ 2 * x ^ 2 := by
  have h1 : min δ |x| ≤ δ := min_le_left _ _
  have h2 : 0 ≤ min δ |x| := le_min hδ (abs_nonneg x)
  rw [mul_pow, ← abs_sq x, abs_pow, sq_abs]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h2 h1 2) (sq_nonneg _)

end StatisticalRL.Probability.Stein

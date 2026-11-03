import Formalization.Generative.GenerativeLowerBoundOverlapTesting
import Formalization.Generative.PolicyEvaluationSampleAssembly

/-! Finite chi-square, overlap and strict estimation testing. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- The finite chi-square expression is oriented from u to the positive
baseline v. -/
noncomputable def finiteChiSquared {ι : Type*} [Fintype ι] (u v : ι → ℝ) : ℝ :=
  ∑ i, v i * (u i / v i - 1) ^ 2

/-- Positive baseline and finite chi-square at most one force overlap at least
one half. This is the finite TV≤sqrt(chi²)/2 argument without a TV API. -/
theorem finite_overlap_ge_half_of_chi_le_one {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 < v i)
    (hu1 : ∑ i, u i = 1) (hv1 : ∑ i, v i = 1)
    (hχ : finiteChiSquared u v ≤ 1) :
    (1 : ℝ) / 2 ≤ ∑ i, min (u i) (v i) := by
  let a : ι → ℝ := fun i ↦ Real.sqrt (v i) * |u i / v i - 1|
  let b : ι → ℝ := fun i ↦ Real.sqrt (v i)
  have ha (i : ι) : a i ^ 2 = v i * (u i / v i - 1) ^ 2 := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (hv i).le, sq_abs]
  have hb (i : ι) : b i ^ 2 = v i := Real.sq_sqrt (hv i).le
  have hab (i : ι) : a i * b i = |u i - v i| := by
    dsimp [a,b]
    have hv0 := ne_of_gt (hv i)
    have heq : (u i / v i - 1) = (u i - v i) / v i := by field_simp
    rw [heq, abs_div, abs_of_pos (hv i)]
    have hsq := Real.sq_sqrt (hv i).le
    field_simp
    have hh := congrArg (fun t : ℝ ↦ t * |u i - v i|) hsq
    nlinarith
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  simp_rw [ha, hb, hab] at hc
  rw [hv1] at hc
  have hnorm : (∑ i, |u i - v i|) ^ 2 ≤ 1 := by
    unfold finiteChiSquared at hχ
    nlinarith
  have hnon : 0 ≤ ∑ i, |u i - v i| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  have hdist : (∑ i, |u i - v i|) ≤ 1 := by nlinarith
  have hmin (i : ι) : min (u i) (v i) = (u i + v i - |u i - v i|) / 2 := by
    rcases le_total (u i) (v i) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp_rw [hmin, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hu1, hv1]
  linarith

/-- If one common estimator is ε-accurate under a baseline and an alternative
whose target differs by more than 2ε, their baseline-distance test must be
correct; test errors are included in strict >ε estimation-risk events. -/
theorem baselineDistanceTest_error_subsets {Ω E : Type*} [NormedAddCommGroup E]
    (estimate : Ω → E) (v₀ v₁ : E) (ε : ℝ) (hsep : 2 * ε < ‖v₁ - v₀‖) :
    (∀ x, ¬ ‖estimate x - v₀‖ ≤ ε → ε < ‖estimate x - v₀‖) ∧
    (∀ x, ‖estimate x - v₀‖ ≤ ε → ε < ‖estimate x - v₁‖) := by
  constructor
  · intro x hx; exact lt_of_not_ge hx
  · intro x hx
    have htri : ‖v₁ - v₀‖ ≤ ‖estimate x - v₁‖ + ‖estimate x - v₀‖ := by
      have hh := norm_add_le (v₁ - estimate x) (estimate x - v₀)
      simpa [sub_add_sub_cancel, norm_sub_rev] using hh
    linarith

end StatisticalRL.GenerativeLowerBound

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weighted `L²` seminorms on finite sample spaces

Reusable elementary facts for second-moment arguments on finite probability spaces given by an
explicit weight vector `w : Ω → ℝ` (for example the i.i.d. path weights of a sampling law).

* `weightedL2 w f = √(∑ ω, w ω * f ω ^ 2)`, with the Minkowski inequalities
  `weightedL2_add_le` and `weightedL2_sum_le`, homogeneity `weightedL2_const_mul`, and the bound
  `weightedL2_le_of_abs_le` for pathwise-bounded `f`.
* `sum_mul_sq_sub_mean_eq`: for a probability vector `p`, `∑ p (f − E f)² = ∑ p f² − (E f)²`,
  hence `sum_mul_sq_sub_mean_le` (variance ≤ second moment).

`sum_mul_sq_sub_mean_le` is the `c = 0` case of `StatisticalRL.Probability.sum_sq_sub_mean_le`
(`Formalization/Probability/MixtureVariance.lean`); it is kept here so this module needs Mathlib only.
-/

open Finset

namespace StatisticalRL.Probability

variable {Ω ι : Type*} [Fintype Ω]

/-- The weighted `L²` seminorm `√(∑ ω, w ω * f ω ^ 2)`. -/
noncomputable def weightedL2 (w f : Ω → ℝ) : ℝ := √(∑ ω, w ω * f ω ^ 2)

theorem weightedL2_nonneg (w f : Ω → ℝ) : 0 ≤ weightedL2 w f := Real.sqrt_nonneg _

theorem sq_weightedL2 {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (f : Ω → ℝ) :
    weightedL2 w f ^ 2 = ∑ ω, w ω * f ω ^ 2 :=
  Real.sq_sqrt (sum_nonneg fun ω _ ↦ mul_nonneg (hw ω) (sq_nonneg _))

/-- Cauchy–Schwarz for the weighted inner product. -/
theorem sum_mul_mul_le_weightedL2 {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (f g : Ω → ℝ) :
    ∑ ω, w ω * (f ω * g ω) ≤ weightedL2 w f * weightedL2 w g := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt univ (fun ω ↦ √(w ω) * f ω) (fun ω ↦ √(w ω) * g ω)
  simp only [mul_pow, Real.sq_sqrt (hw _)] at h
  refine le_of_eq_of_le ?_ h
  refine sum_congr rfl fun ω _ ↦ ?_
  rw [show √(w ω) * f ω * (√(w ω) * g ω) = (√(w ω) * √(w ω)) * (f ω * g ω) by ring,
    Real.mul_self_sqrt (hw ω)]

/-- Minkowski's inequality for the weighted `L²` seminorm. -/
theorem weightedL2_add_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (f g : Ω → ℝ) :
    weightedL2 w (f + g) ≤ weightedL2 w f + weightedL2 w g := by
  have hcs := sum_mul_mul_le_weightedL2 hw f g
  have hf := sq_weightedL2 hw f
  have hg := sq_weightedL2 hw g
  have hexp : ∑ ω, w ω * (f + g) ω ^ 2 =
      ∑ ω, w ω * f ω ^ 2 + 2 * ∑ ω, w ω * (f ω * g ω) + ∑ ω, w ω * g ω ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun ω _ ↦ by simp only [Pi.add_apply]; ring
  have hsum : ∑ ω, w ω * (f + g) ω ^ 2 ≤ (weightedL2 w f + weightedL2 w g) ^ 2 := by
    rw [hexp, add_sq, ← hf, ← hg]
    nlinarith
  calc weightedL2 w (f + g) ≤ √((weightedL2 w f + weightedL2 w g) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = weightedL2 w f + weightedL2 w g :=
        Real.sqrt_sq (add_nonneg (weightedL2_nonneg _ _) (weightedL2_nonneg _ _))

theorem weightedL2_add₄_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (f₁ f₂ f₃ f₄ : Ω → ℝ) :
    weightedL2 w (f₁ + f₂ + f₃ + f₄) ≤
      weightedL2 w f₁ + weightedL2 w f₂ + weightedL2 w f₃ + weightedL2 w f₄ := by
  have e1 := weightedL2_add_le hw (f₁ + f₂ + f₃) f₄
  have e2 := weightedL2_add_le hw (f₁ + f₂) f₃
  have e3 := weightedL2_add_le hw f₁ f₂
  linarith

theorem weightedL2_zero (w : Ω → ℝ) : weightedL2 w (fun _ ↦ (0 : ℝ)) = 0 := by
  simp [weightedL2]

/-- Minkowski's inequality for a finite sum of functions. -/
theorem weightedL2_sum_le {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (s : Finset ι) (F : ι → Ω → ℝ) :
    weightedL2 w (fun ω ↦ ∑ j ∈ s, F j ω) ≤ ∑ j ∈ s, weightedL2 w (F j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightedL2_zero]
  | insert j s hj ih =>
    rw [sum_insert hj]
    have h : (fun ω ↦ ∑ k ∈ insert j s, F k ω) = F j + fun ω ↦ ∑ k ∈ s, F k ω := by
      funext ω; simp [sum_insert hj]
    rw [h]
    exact (weightedL2_add_le hw _ _).trans (add_le_add le_rfl ih)

theorem weightedL2_const_mul {w : Ω → ℝ} (c : ℝ) (f : Ω → ℝ) :
    weightedL2 w (fun ω ↦ c * f ω) = |c| * weightedL2 w f := by
  simp only [weightedL2, mul_pow, ← sq_abs c]
  simp_rw [show ∀ ω, w ω * (|c| ^ 2 * f ω ^ 2) = |c| ^ 2 * (w ω * f ω ^ 2) from fun ω ↦ by ring]
  rw [← mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg c)]

/-- Monotonicity in the absolute value. -/
theorem weightedL2_mono {w f g : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (h : ∀ ω, |f ω| ≤ |g ω|) :
    weightedL2 w f ≤ weightedL2 w g := by
  refine Real.sqrt_le_sqrt (sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left ?_ (hw ω))
  rw [← sq_abs (f ω), ← sq_abs (g ω)]
  exact pow_le_pow_left₀ (abs_nonneg _) (h ω) 2

theorem weightedL2_abs (w f : Ω → ℝ) : weightedL2 w (fun ω ↦ |f ω|) = weightedL2 w f := by
  simp only [weightedL2, sq_abs]

theorem weightedL2_neg (w f : Ω → ℝ) : weightedL2 w (fun ω ↦ -f ω) = weightedL2 w f := by
  simp only [weightedL2, neg_sq]

theorem weightedL2_le_sqrt {w f : Ω → ℝ} {c : ℝ} (h : ∑ ω, w ω * f ω ^ 2 ≤ c) :
    weightedL2 w f ≤ √c :=
  Real.sqrt_le_sqrt h

/-- A pathwise bound `|f| ≤ D` gives `‖f‖_{L²(w)} ≤ D` when `∑ w = 1`. -/
theorem weightedL2_le_of_abs_le {w f : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    {D : ℝ} (hD : 0 ≤ D) (hf : ∀ ω, |f ω| ≤ D) : weightedL2 w f ≤ D := by
  have h : ∑ ω, w ω * f ω ^ 2 ≤ D ^ 2 := by
    calc ∑ ω, w ω * f ω ^ 2 ≤ ∑ ω, w ω * D ^ 2 := by
          refine sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left ?_ (hw ω)
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hf ω) 2
      _ = D ^ 2 := by rw [← sum_mul, hw1, one_mul]
  exact (weightedL2_le_sqrt h).trans_eq (Real.sqrt_sq hD)

/-- Second moment bound from a pathwise square bound. -/
theorem sum_mul_sq_le_of_abs_le {w f : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    {D : ℝ} (hf : ∀ ω, |f ω| ≤ D) : ∑ ω, w ω * f ω ^ 2 ≤ D ^ 2 := by
  calc ∑ ω, w ω * f ω ^ 2 ≤ ∑ ω, w ω * D ^ 2 := by
        refine sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left ?_ (hw ω)
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hf ω) 2
    _ = D ^ 2 := by rw [← sum_mul, hw1, one_mul]

/-- Variance identity for a probability vector: `∑ p (f − E f)² = ∑ p f² − (E f)²`. -/
theorem sum_mul_sq_sub_mean_eq {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1) (f : Ω → ℝ) :
    ∑ ω, p ω * (f ω - ∑ ω', p ω' * f ω') ^ 2 =
      ∑ ω, p ω * f ω ^ 2 - (∑ ω, p ω * f ω) ^ 2 := by
  set m := ∑ ω', p ω' * f ω'
  have h : ∀ ω, p ω * (f ω - m) ^ 2 = p ω * f ω ^ 2 - 2 * m * (p ω * f ω) + m ^ 2 * p ω :=
    fun ω ↦ by ring
  simp_rw [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, hp1]
  ring

/-- Variance is at most the second moment. -/
theorem sum_mul_sq_sub_mean_le {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1) (f : Ω → ℝ) :
    ∑ ω, p ω * (f ω - ∑ ω', p ω' * f ω') ^ 2 ≤ ∑ ω, p ω * f ω ^ 2 := by
  rw [sum_mul_sq_sub_mean_eq hp1]
  linarith [sq_nonneg (∑ ω, p ω * f ω)]

end StatisticalRL.Probability

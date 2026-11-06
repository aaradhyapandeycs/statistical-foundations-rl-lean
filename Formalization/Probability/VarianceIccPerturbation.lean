import Formalization.Probability.Variance
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Sharp variance perturbation on a nonnegative range

Used by the proof of Lemma 6.6 (`chapters/offlineRL.tex:4034–4068`,
`eq:Var-perturbation-V-su-inf`): for vectors with entries in `[0, C]` that are `ε`-close, the
variances differ by at most `2Cε`. The argument is the source's: the mean minimizes the
expected squared deviation.
-/

namespace StatisticalRL.FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

/-- The variance is at most the expected squared deviation from any constant. -/
theorem variance_le_expectation_sub_sq (d : FiniteDistribution Ω) (f : Ω → ℝ) (c : ℝ) :
    d.variance f ≤ d.expectation (fun x ↦ (f x - c) ^ 2) := by
  have hexpand : (fun x ↦ (f x - c) ^ 2) = (fun x ↦ f x ^ 2 - (2 * c) * f x + c ^ 2) := by
    funext x
    ring
  rw [hexpand, expectation_add, expectation_sub, expectation_mul, expectation_const]
  unfold variance
  nlinarith [sq_nonneg (d.expectation f - c)]

/-- One-sided sharp perturbation bound. -/
theorem variance_le_variance_add_of_Icc (d : FiniteDistribution Ω) {f g : Ω → ℝ} {C ε : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc 0 C) (hg : ∀ x, g x ∈ Set.Icc 0 C)
    (hfg : ∀ x, |f x - g x| ≤ ε) :
    d.variance f ≤ d.variance g + 2 * C * ε := by
  have hm0 : 0 ≤ d.expectation g := d.expectation_nonneg fun x ↦ (hg x).1
  have hmC : d.expectation g ≤ C := d.expectation_le_const fun x ↦ (hg x).2
  have hpoint : ∀ x, (f x - d.expectation g) ^ 2 ≤
      (g x - d.expectation g) ^ 2 + 2 * C * ε := by
    intro x
    have hsum : |f x + g x - 2 * d.expectation g| ≤ 2 * C := by
      rw [abs_le]
      constructor <;> linarith [(hf x).1, (hf x).2, (hg x).1, (hg x).2]
    have hprod : (f x - d.expectation g) ^ 2 - (g x - d.expectation g) ^ 2 =
        (f x - g x) * (f x + g x - 2 * d.expectation g) := by ring
    have habs : |(f x - g x) * (f x + g x - 2 * d.expectation g)| ≤ ε * (2 * C) := by
      rw [abs_mul]
      exact mul_le_mul (hfg x) hsum (abs_nonneg _) ((abs_nonneg _).trans (hfg x))
    have := le_abs_self ((f x - g x) * (f x + g x - 2 * d.expectation g))
    linarith
  calc
    d.variance f ≤ d.expectation (fun x ↦ (f x - d.expectation g) ^ 2) :=
      d.variance_le_expectation_sub_sq f _
    _ ≤ d.expectation (fun x ↦ (g x - d.expectation g) ^ 2 + 2 * C * ε) :=
      d.expectation_mono hpoint
    _ = d.variance g + 2 * C * ε := by
      rw [expectation_add, expectation_const, ← d.variance_eq_expectation_centered_sq]

/-- Sharp perturbation `|Var f − Var g| ≤ 2Cε` for `[0, C]`-valued vectors. -/
theorem abs_variance_sub_le_of_Icc (d : FiniteDistribution Ω) {f g : Ω → ℝ} {C ε : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc 0 C) (hg : ∀ x, g x ∈ Set.Icc 0 C)
    (hfg : ∀ x, |f x - g x| ≤ ε) :
    |d.variance f - d.variance g| ≤ 2 * C * ε := by
  have h1 := d.variance_le_variance_add_of_Icc hf hg hfg
  have h2 := d.variance_le_variance_add_of_Icc hg hf fun x ↦ by rw [abs_sub_comm]; exact hfg x
  rw [abs_le]
  constructor <;> linarith

end StatisticalRL.FiniteDistribution

namespace StatisticalRL

/-- Subadditivity of the real square root. -/
theorem sqrt_add_le_sqrt_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hx' := Real.sq_sqrt hx
  have hy' := Real.sq_sqrt hy
  nlinarith [mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

end StatisticalRL

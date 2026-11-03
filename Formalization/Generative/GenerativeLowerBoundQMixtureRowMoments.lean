import Formalization.Generative.GenerativeLowerBoundQMixtureLikelihood
import Formalization.Generative.GenerativeLowerBoundProductKL
import Mathlib.MeasureTheory.Integral.Pi

/-! Actual Bernoulli row likelihood moments, including the empty row. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- A single changed Bernoulli coordinate has mean-one likelihood under the
actual baseline law. -/
theorem qMixtureBernoulliLikelihood_integral (p q : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1) :
    ∫ b, qMixtureBernoulliLikelihood (p : ℝ) (q : ℝ) b
      ∂(PMF.bernoulli p hp1.le).toMeasure = 1 := by
  rw [PMF.integral_eq_sum]
  simp only [Fintype.sum_bool, smul_eq_mul]
  simp [PMF.bernoulli_apply, qMixtureBernoulliLikelihood, hp1.le]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have hp10 : 1 - (p : ℝ) ≠ 0 := by
    have hh : (p : ℝ) < 1 := by exact_mod_cast hp1
    linarith
  field_simp
  ring

/-- Exact one-coordinate squared likelihood moment under the baseline law. -/
theorem qMixtureBernoulliLikelihood_sq_integral (p q : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1) :
    ∫ b, (qMixtureBernoulliLikelihood (p : ℝ) (q : ℝ) b) ^ 2
      ∂(PMF.bernoulli p hp1.le).toMeasure =
        1 + ((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ))) := by
  rw [PMF.integral_eq_sum]
  simp only [Fintype.sum_bool, smul_eq_mul]
  simpa [PMF.bernoulli_apply, hp1.le, qMixtureBernoulliLikelihood] using
    qMixture_bernoulli_likelihood_second_moment (p : ℝ) (q : ℝ)
      (by exact_mod_cast hp) (by exact_mod_cast hp1)

/-- The actual N-fold baseline row law has exactly the Nth-power diagonal
likelihood moment. The statement includes N=0. -/
theorem qMixtureRowLikelihood_sq_integral (N : ℕ) (p q : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1) :
    ∫ x, (qMixtureRowLikelihood N (p : ℝ) (q : ℝ) x) ^ 2
      ∂(bernoulliProductLaw N p hp1.le) =
      (1 + ((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ)))) ^ N := by
  unfold qMixtureRowLikelihood bernoulliProductLaw
  simp_rw [← Finset.prod_pow]
  have hprod := integral_fintype_prod_eq_prod
    (μ := fun _ : Fin N ↦ (PMF.bernoulli p hp1.le).toMeasure)
    (fun (_ : Fin N) (b : Bool) ↦ (qMixtureBernoulliLikelihood (p : ℝ) (q : ℝ) b) ^ 2)
  rw [hprod]
  simp [qMixtureBernoulliLikelihood_sq_integral p q hp hp1 hq1]

end StatisticalRL.GenerativeLowerBound

import Formalization.Generative.GenerativeLowerBoundQMixtureAtomRatio

/-! Diagonal likelihood moment on the actual full active product. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- The full active baseline product gives the same diagonal moment as the
changed N-sample row; all other coordinates integrate to one. -/
theorem qMixture_active_row_diagonal_moment {m A N : ℕ} [NeZero m] [NeZero A]
    (p q : ℝ≥0) (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1)
    (θ : Fin m × Fin A) :
    ∫ x, (qMixtureRowLikelihoodOnArray (p : ℝ) (q : ℝ) θ x) ^ 2
      ∂(qMixtureActiveBaseline (m := m) (A := A) (N := N) p q hp1.le hq1) =
      (1 + ((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ)))) ^ N := by
  classical
  let f (z : QMixtureActiveCoordinates m A N) (b : Bool) : ℝ :=
    if z.1 = θ then (qMixtureBernoulliLikelihood (p : ℝ) (q : ℝ) b) ^ 2 else 1
  have hfactor (x : QMixtureActiveCoordinates m A N → Bool) :
      (qMixtureRowLikelihoodOnArray (p : ℝ) (q : ℝ) θ x) ^ 2 = ∏ z, f z (x z) := by
    unfold qMixtureRowLikelihoodOnArray qMixtureRowLikelihood
    rw [← Finset.prod_pow, qMixture_product_restrict_row]
  simp_rw [hfactor]
  unfold qMixtureActiveBaseline indexedBernoulliLaw
  simp only [qMixtureBernoulliParameter, Option.noConfusion, ↓reduceIte]
  rw [integral_fintype_prod_eq_prod]
  have hcoord (z : QMixtureActiveCoordinates m A N) :
      (∫ b, f z b ∂(PMF.bernoulli p hp1.le).toMeasure) =
        if z.1 = θ then 1 + ((q : ℝ) - (p : ℝ)) ^ 2 /
          ((p : ℝ) * (1 - (p : ℝ))) else 1 := by
    by_cases hz : z.1 = θ
    · simp [f, hz, qMixtureBernoulliLikelihood_sq_integral p q hp hp1 hq1]
    · simp only [f, hz, ↓reduceIte, integral_const, smul_eq_mul, mul_one]
      rw [probReal_univ]
  change (∏ z : QMixtureActiveCoordinates m A N,
    ∫ b, f z b ∂(PMF.bernoulli p hp1.le).toMeasure) = _
  simp_rw [hcoord]
  rw [qMixture_product_one_changed_row θ (fun _ ↦
    1 + ((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ))))]
  simp

end StatisticalRL.GenerativeLowerBound

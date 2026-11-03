import Formalization.Generative.GenerativeLowerBoundQMixtureChiAlgebra
import Formalization.Generative.GenerativeLowerBoundQMixtureTesting

/-! Actual active-product mean likelihood and finite-mixture moments. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- Each changed-row likelihood has mean one under the actual full active
baseline product, including N=0. -/
theorem qMixture_active_row_mean {m A N : ℕ} [NeZero m] [NeZero A]
    (p q : ℝ≥0) (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1)
    (θ : Fin m × Fin A) :
    ∫ x, qMixtureRowLikelihoodOnArray (p : ℝ) (q : ℝ) θ x
      ∂(qMixtureActiveBaseline (m := m) (A := A) (N := N) p q hp1.le hq1) = 1 := by
  classical
  let f (z : QMixtureActiveCoordinates m A N) (b : Bool) : ℝ :=
    if z.1 = θ then qMixtureBernoulliLikelihood (p : ℝ) (q : ℝ) b else 1
  have hf (x : QMixtureActiveCoordinates m A N → Bool) :
      qMixtureRowLikelihoodOnArray (p : ℝ) (q : ℝ) θ x = ∏ z, f z (x z) := by
    unfold qMixtureRowLikelihoodOnArray qMixtureRowLikelihood
    rw [qMixture_product_restrict_row]
  simp_rw [hf]
  unfold qMixtureActiveBaseline indexedBernoulliLaw
  rw [integral_fintype_prod_eq_prod]
  apply Finset.prod_eq_one
  intro z _
  by_cases hz : z.1 = θ
  · simpa [f, hz, qMixtureBernoulliParameter] using
      qMixtureBernoulliLikelihood_integral p q hp hp1 hq1
  · simp only [f, hz, ↓reduceIte, integral_const, smul_eq_mul, mul_one]
    rw [probReal_univ]

end StatisticalRL.GenerativeLowerBound

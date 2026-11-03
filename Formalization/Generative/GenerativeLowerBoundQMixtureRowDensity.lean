import Formalization.Generative.GenerativeLowerBoundQMixtureRowMoments
import Formalization.Generative.GenerativeLowerBoundQMixtureLaw

/-! Actual Bernoulli atom ratios and normalized row likelihood. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- Actual Bernoulli atom ratio agrees with the staged real likelihood factor.
The strict p range makes both baseline atom denominators positive. -/
theorem qMixtureBernoulli_atom_ratio (p q : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1) (b : Bool) :
    (((PMF.bernoulli q hq1).toMeasure {b}) /
      ((PMF.bernoulli p hp1.le).toMeasure {b})).toReal =
        qMixtureBernoulliLikelihood (p : ℝ) (q : ℝ) b := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), ENNReal.toReal_div]
  cases b <;> simp [PMF.bernoulli_apply, qMixtureBernoulliLikelihood, hp1.le, hq1]

/-- The actual N-fold row likelihood is normalized under the baseline,
including the empty product N=0. -/
theorem qMixtureRowLikelihood_integral (N : ℕ) (p q : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1) :
    ∫ x, qMixtureRowLikelihood N (p : ℝ) (q : ℝ) x
      ∂(bernoulliProductLaw N p hp1.le) = 1 := by
  unfold qMixtureRowLikelihood bernoulliProductLaw
  have hprod := integral_fintype_prod_eq_prod
    (μ := fun _ : Fin N ↦ (PMF.bernoulli p hp1.le).toMeasure)
    (fun (_ : Fin N) (b : Bool) ↦ qMixtureBernoulliLikelihood (p : ℝ) (q : ℝ) b)
  rw [hprod]
  simp [qMixtureBernoulliLikelihood_integral p q hp hp1 hq1]

end StatisticalRL.GenerativeLowerBound

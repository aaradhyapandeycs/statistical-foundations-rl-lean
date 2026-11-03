import Formalization.Generative.GenerativeLowerBoundQMixtureProductFactors

/-! Exact actual active-product atom likelihood for a changed row. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- The actual alternative-to-baseline atom ratio is exactly the row
likelihood product. Baseline is strictly interior, and N=0 is included. -/
theorem qMixtureActiveAlternative_atom_ratio {m A N : ℕ} [NeZero m] [NeZero A]
    (p q : ℝ≥0) (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1)
    (θ : Fin m × Fin A) (x : QMixtureActiveCoordinates m A N → Bool) :
    ((qMixtureActiveAlternative p q hp1.le hq1 θ {x}) /
      (qMixtureActiveBaseline p q hp1.le hq1 {x})).toReal =
        qMixtureRowLikelihoodOnArray (p : ℝ) (q : ℝ) θ x := by
  classical
  let B (z : QMixtureActiveCoordinates m A N) := (PMF.bernoulli p hp1.le).toMeasure
  let C (z : QMixtureActiveCoordinates m A N) :=
    (PMF.bernoulli (qMixtureBernoulliParameter (some θ) p q z)
      (qMixtureBernoulliParameter_le_one (some θ) p q hp1.le hq1 z)).toMeasure
  have hratio : qMixtureActiveAlternative p q hp1.le hq1 θ {x} /
      qMixtureActiveBaseline p q hp1.le hq1 {x} = ∏ z, C z {x z} / B z {x z} := by
    unfold qMixtureActiveAlternative qMixtureActiveBaseline indexedBernoulliLaw
    rw [Measure.pi_singleton, Measure.pi_singleton]
    exact (ENNReal.prod_div_distrib_of_ne_top (fun z _ ↦ measure_ne_top (B z) {x z})).symm
  rw [hratio, ENNReal.toReal_prod]
  unfold qMixtureRowLikelihoodOnArray qMixtureRowLikelihood
  rw [← qMixture_product_restrict_row θ (fun z ↦
    qMixtureBernoulliLikelihood (p : ℝ) (q : ℝ) (x z))]
  apply Finset.prod_congr rfl
  intro z _
  by_cases hz : z.1 = θ
  · subst θ
    simpa [C, B, qMixtureBernoulliParameter] using
      qMixtureBernoulli_atom_ratio p q hp hp1 hq1 (x z)
  · have hB : B z {x z} ≠ 0 := by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      apply (PMF.mem_support_iff _ _).1
      rw [bernoulli_fullSupport p hp hp1]
      trivial
    have hBr : (B z {x z}).toReal ≠ 0 :=
      ne_of_gt (ENNReal.toReal_pos hB (measure_ne_top (B z) _))
    have hC : C z = B z := by simp [C, B, qMixtureBernoulliParameter, Ne.symm hz]
    rw [hC, ENNReal.toReal_div, div_self hBr]
    simp [hz]

end StatisticalRL.GenerativeLowerBound

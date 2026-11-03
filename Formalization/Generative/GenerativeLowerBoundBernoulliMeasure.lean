import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Formalization.Generative.GenerativeLowerBoundBernoulli

/-! Measure-level Bernoulli relative entropy, on the actual Bool law. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace StatisticalRL.GenerativeLowerBound

/-- A full-support Boolean PMF assigns positive mass to both atoms. -/
theorem bernoulli_fullSupport (p : ℝ≥0) (hp : 0 < p) (hp1 : p < 1) :
    (PMF.bernoulli p hp1.le).support = Set.univ := by
  ext b
  cases b <;> simp [ne_of_gt hp, ne_of_lt hp1]

/-- Interior Bernoulli measures are mutually absolutely continuous. -/
theorem bernoulli_measure_ac (q p : ℝ≥0) (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1) :
    (PMF.bernoulli q hq1).toMeasure ≪ (PMF.bernoulli p hp1.le).toMeasure := by
  intro s hs
  have hdis := (PMF.toMeasure_apply_eq_zero_iff _ (Set.to_countable s).measurableSet).1 hs
  rw [bernoulli_fullSupport p hp hp1] at hdis
  have hs0 : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b hb
    exact (Set.disjoint_left.mp hdis) (Set.mem_univ b) hb
  simp [hs0]

/-- For full-support finite PMFs, the Radon–Nikodym derivative is the ratio
of atom masses, at every atom. -/
theorem pmf_rnDeriv_apply (P Q : PMF Bool) (hQ : ∀ b, Q b ≠ 0)
    (hac : P.toMeasure ≪ Q.toMeasure) (b : Bool) :
    P.toMeasure.rnDeriv Q.toMeasure b = P b / Q b := by
  have h := Measure.setLIntegral_rnDeriv hac ({b} : Set Bool)
  rw [lintegral_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at h
  apply (ENNReal.eq_div_iff (hQ b) (PMF.apply_ne_top Q b)).2
  simpa [mul_comm] using h

/-- Mathlib relative entropy of the actual Bernoulli laws equals the
reviewed scalar expression. -/
theorem bernoulli_toReal_klDiv_eq_expression (q p : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq1 : q < 1) :
    (InformationTheory.klDiv (PMF.bernoulli q hq1.le).toMeasure
      (PMF.bernoulli p hp1.le).toMeasure).toReal =
      bernoulliKLExpression (q : ℝ) (p : ℝ) := by
  let P := PMF.bernoulli q hq1.le
  let Q := PMF.bernoulli p hp1.le
  have hQ : ∀ b, Q b ≠ 0 := by
    intro b
    have hs : b ∈ Q.support := by rw [bernoulli_fullSupport p hp hp1]; trivial
    exact (PMF.mem_support_iff Q b).1 hs
  have hac : P.toMeasure ≪ Q.toMeasure := bernoulli_measure_ac q p hp hp1 hq1.le
  have heq : P.toMeasure Set.univ = Q.toMeasure Set.univ := by
    rw [measure_univ, measure_univ]
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac heq, PMF.integral_eq_sum]
  simp only [Fintype.sum_bool, smul_eq_mul, MeasureTheory.llr, pmf_rnDeriv_apply P Q hQ hac]
  simp [P, Q, PMF.bernoulli_apply, ENNReal.toReal_div, bernoulliKLExpression,
    hp1.le, hq1.le]

/-- The source one-sample quadratic estimate for actual Bernoulli laws. -/
theorem bernoulli_toReal_klDiv_le_quadratic (q p : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    (InformationTheory.klDiv (PMF.bernoulli q hq1.le).toMeasure
      (PMF.bernoulli p hp1.le).toMeasure).toReal ≤
      ((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ))) := by
  rw [bernoulli_toReal_klDiv_eq_expression q p hp hp1 hq1]
  apply bernoulliKLExpression_le_quadratic
  · exact_mod_cast hp
  · exact_mod_cast hp1
  · exact_mod_cast hq
  · exact_mod_cast hq1

/-- The divergence is finite, so conversion to real loses no information. -/
theorem bernoulli_klDiv_ne_top (q p : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq1 : q < 1) :
    InformationTheory.klDiv (PMF.bernoulli q hq1.le).toMeasure
      (PMF.bernoulli p hp1.le).toMeasure ≠ ⊤ := by
  apply InformationTheory.klDiv_ne_top_iff.mpr
  exact ⟨bernoulli_measure_ac q p hp hp1 hq1.le, Integrable.of_finite⟩

/-- The ℝ≥0∞ divergence itself equals the lifted scalar expression. -/
theorem bernoulli_klDiv_eq_expression (q p : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq1 : q < 1) :
    InformationTheory.klDiv (PMF.bernoulli q hq1.le).toMeasure
      (PMF.bernoulli p hp1.le).toMeasure =
      ENNReal.ofReal (bernoulliKLExpression (q : ℝ) (p : ℝ)) := by
  rw [← bernoulli_toReal_klDiv_eq_expression q p hp hp1 hq1,
    ENNReal.ofReal_toReal (bernoulli_klDiv_ne_top q p hp hp1 hq1)]

end StatisticalRL.GenerativeLowerBound

import Formalization.Generative.GenerativeLowerBoundBernoulliMeasure
import Mathlib.MeasureTheory.Constructions.Pi

/-! Relative-entropy tensorization for genuine finite product experiments. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- On a finite discrete space, a measure positive on every atom dominates
any measure. -/
theorem finite_fullSupport_ac {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ ν : Measure Ω) (hν : ∀ x, ν {x} ≠ 0) : μ ≪ ν := by
  intro s hs
  have hs0 : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hν x (measure_mono_null (Set.singleton_subset_iff.mpr hx) hs)
  simp [hs0]

/-- Atomic Radon–Nikodym ratio for finite full-support probability measures. -/
theorem finite_rnDeriv_apply {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ∀ x, ν {x} ≠ 0) (x : Ω) :
    μ.rnDeriv ν x = μ {x} / ν {x} := by
  have hac := finite_fullSupport_ac μ ν hν
  have h := Measure.setLIntegral_rnDeriv hac ({x} : Set Ω)
  rw [lintegral_singleton] at h
  apply (ENNReal.eq_div_iff (hν x) (measure_ne_top ν _)).2
  simpa [mul_comm] using h

/-- The actual experiment consists of N independent Bernoulli draws. -/
noncomputable def bernoulliProductLaw (N : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    Measure (Fin N → Bool) := Measure.pi (fun _ : Fin N ↦ (PMF.bernoulli p hp).toMeasure)

instance bernoulliProductLaw_probability (N : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernoulliProductLaw N p hp) := by
  unfold bernoulliProductLaw
  infer_instance

/-- Each N-sample atom has positive probability for an interior parameter. -/
theorem bernoulliProductLaw_atom_ne_zero (N : ℕ) (p : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (x : Fin N → Bool) :
    bernoulliProductLaw N p hp1.le {x} ≠ 0 := by
  unfold bernoulliProductLaw
  rw [Measure.pi_singleton]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  apply (PMF.mem_support_iff _ _).1
  rw [bernoulli_fullSupport p hp hp1]
  trivial

/-- Log-likelihood of the N-sample product equals the sum of single-sample
log-likelihoods, at every observation. -/
theorem bernoulliProduct_llr (N : ℕ) (q p : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1)
    (x : Fin N → Bool) :
    MeasureTheory.llr (bernoulliProductLaw N q hq1.le) (bernoulliProductLaw N p hp1.le) x =
      ∑ i : Fin N, MeasureTheory.llr (PMF.bernoulli q hq1.le).toMeasure
        (PMF.bernoulli p hp1.le).toMeasure (x i) := by
  let P := (PMF.bernoulli q hq1.le).toMeasure
  let Q := (PMF.bernoulli p hp1.le).toMeasure
  have hP (b : Bool) : P {b} ≠ 0 := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    apply (PMF.mem_support_iff _ _).1
    rw [bernoulli_fullSupport q hq hq1]
    trivial
  have hQ (b : Bool) : Q {b} ≠ 0 := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    apply (PMF.mem_support_iff _ _).1
    rw [bernoulli_fullSupport p hp hp1]
    trivial
  have hQprod := bernoulliProductLaw_atom_ne_zero N p hp hp1
  have hratio : (bernoulliProductLaw N q hq1.le) {x} /
      (bernoulliProductLaw N p hp1.le) {x} = ∏ i : Fin N, (P {x i} / Q {x i}) := by
    unfold bernoulliProductLaw
    rw [Measure.pi_singleton, Measure.pi_singleton]
    exact (ENNReal.prod_div_distrib_of_ne_top (fun i _ ↦ measure_ne_top Q {x i})).symm
  have hratios (i : Fin N) : ((P {x i} / Q {x i}).toReal) ≠ 0 := by
    rw [ENNReal.toReal_div]
    exact div_ne_zero (ne_of_gt (ENNReal.toReal_pos (hP _) (measure_ne_top P _)))
      (ne_of_gt (ENNReal.toReal_pos (hQ _) (measure_ne_top Q _)))
  rw [MeasureTheory.llr, finite_rnDeriv_apply _ _ hQprod, hratio,
    ENNReal.toReal_prod, Real.log_prod (fun i _ ↦ hratios i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.llr, finite_rnDeriv_apply P Q hQ]

/-- Actual N-fold product Bernoulli relative entropy tensorizes exactly. -/
theorem bernoulliProduct_toReal_klDiv (N : ℕ) (q p : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    (InformationTheory.klDiv (bernoulliProductLaw N q hq1.le)
      (bernoulliProductLaw N p hp1.le)).toReal =
      N * (InformationTheory.klDiv (PMF.bernoulli q hq1.le).toMeasure
        (PMF.bernoulli p hp1.le).toMeasure).toReal := by
  let μ := bernoulliProductLaw N q hq1.le
  let ν := bernoulliProductLaw N p hp1.le
  let P := (PMF.bernoulli q hq1.le).toMeasure
  let Q := (PMF.bernoulli p hp1.le).toMeasure
  have hac : μ ≪ ν := finite_fullSupport_ac μ ν (bernoulliProductLaw_atom_ne_zero N p hp hp1)
  have hac' : P ≪ Q := bernoulli_measure_ac q p hp hp1 hq1.le
  have heq : μ Set.univ = ν Set.univ := by rw [measure_univ, measure_univ]
  have heq' : P Set.univ = Q Set.univ := by rw [measure_univ, measure_univ]
  change (InformationTheory.klDiv μ ν).toReal = N * (InformationTheory.klDiv P Q).toReal
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac heq,
    InformationTheory.toReal_klDiv_of_measure_eq hac' heq']
  have hllr : MeasureTheory.llr μ ν = fun x ↦ ∑ i : Fin N, MeasureTheory.llr P Q (x i) := by
    funext x
    exact bernoulliProduct_llr N q p hp hp1 hq hq1 x
  rw [hllr, integral_finset_sum _ (fun i _ ↦ Integrable.of_finite)]
  have hm (i : Fin N) : (μ.map (fun x ↦ x i)) = P := by
    exact (measurePreserving_eval (fun _ : Fin N ↦ P) i).map_eq
  have hi (i : Fin N) :
      (∫ x, MeasureTheory.llr P Q (x i) ∂μ) = ∫ b, MeasureTheory.llr P Q b ∂P := by
    calc
      _ = ∫ b, MeasureTheory.llr P Q b ∂(μ.map (fun x ↦ x i)) :=
        (integral_map (measurable_pi_apply i).aemeasurable
          (MeasureTheory.stronglyMeasurable_llr P Q).aestronglyMeasurable).symm
      _ = _ := by rw [hm i]
  simp_rw [hi]
  simp

/-- Product KL is finite; the real-valued identity does not hide infinity. -/
theorem bernoulliProduct_klDiv_ne_top (N : ℕ) (q p : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1) :
    InformationTheory.klDiv (bernoulliProductLaw N q hq1)
      (bernoulliProductLaw N p hp1.le) ≠ ⊤ := by
  apply InformationTheory.klDiv_ne_top_iff.mpr
  exact ⟨finite_fullSupport_ac _ _ (bernoulliProductLaw_atom_ne_zero N p hp hp1),
    Integrable.of_finite⟩

/-- Explicit N-sample quadratic bound for the genuine product laws. -/
theorem bernoulliProduct_klDiv_le_quadratic (N : ℕ) (q p : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    (InformationTheory.klDiv (bernoulliProductLaw N q hq1.le)
      (bernoulliProductLaw N p hp1.le)).toReal ≤
      N * (((q : ℝ) - (p : ℝ)) ^ 2 / ((p : ℝ) * (1 - (p : ℝ)))) := by
  rw [bernoulliProduct_toReal_klDiv N q p hp hp1 hq hq1]
  exact mul_le_mul_of_nonneg_left (bernoulli_toReal_klDiv_le_quadratic q p hp hp1 hq hq1)
    (Nat.cast_nonneg N)

end StatisticalRL.GenerativeLowerBound

import Formalization.Generative.GenerativeLowerBoundProductKL

/-! KL tensorization for heterogeneous Bernoulli product experiments. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- Genuine product law for independent Bernoulli coordinates with distinct
parameters. -/
noncomputable def indexedBernoulliLaw {ι : Type*} [Fintype ι]
    (p : ι → ℝ≥0) (hp : ∀ i, p i ≤ 1) : Measure (ι → Bool) :=
  Measure.pi (fun i ↦ (PMF.bernoulli (p i) (hp i)).toMeasure)

instance indexedBernoulliLaw_probability {ι : Type*} [Fintype ι]
    (p : ι → ℝ≥0) (hp : ∀ i, p i ≤ 1) : IsProbabilityMeasure (indexedBernoulliLaw p hp) := by
  unfold indexedBernoulliLaw
  infer_instance

/-- Interior Bernoulli coordinates give strictly positive product atoms. -/
theorem indexedBernoulliLaw_atom_ne_zero {ι : Type*} [Fintype ι]
    (p : ι → ℝ≥0) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (x : ι → Bool) :
    indexedBernoulliLaw p (fun i ↦ (hp1 i).le) {x} ≠ 0 := by
  unfold indexedBernoulliLaw
  rw [Measure.pi_singleton]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  apply (PMF.mem_support_iff _ _).1
  rw [bernoulli_fullSupport (p i) (hp i) (hp1 i)]
  trivial

/-- The joint log-likelihood is the sum of coordinate log-likelihoods. -/
theorem indexedBernoulliLaw_llr {ι : Type*} [Fintype ι]
    (q p : ι → ℝ≥0) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (hq : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) (x : ι → Bool) :
    MeasureTheory.llr (indexedBernoulliLaw q (fun i ↦ (hq1 i).le))
      (indexedBernoulliLaw p (fun i ↦ (hp1 i).le)) x =
      ∑ i, MeasureTheory.llr (PMF.bernoulli (q i) (hq1 i).le).toMeasure
        (PMF.bernoulli (p i) (hp1 i).le).toMeasure (x i) := by
  classical
  let P (i : ι) := (PMF.bernoulli (q i) (hq1 i).le).toMeasure
  let Q (i : ι) := (PMF.bernoulli (p i) (hp1 i).le).toMeasure
  have hP (i : ι) (b : Bool) : P i {b} ≠ 0 := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    apply (PMF.mem_support_iff _ _).1
    rw [bernoulli_fullSupport (q i) (hq i) (hq1 i)]
    trivial
  have hQ (i : ι) (b : Bool) : Q i {b} ≠ 0 := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    apply (PMF.mem_support_iff _ _).1
    rw [bernoulli_fullSupport (p i) (hp i) (hp1 i)]
    trivial
  have hQprod := indexedBernoulliLaw_atom_ne_zero p hp hp1
  have hratio : (indexedBernoulliLaw q (fun i ↦ (hq1 i).le)) {x} /
      (indexedBernoulliLaw p (fun i ↦ (hp1 i).le)) {x} = ∏ i, (P i {x i} / Q i {x i}) := by
    unfold indexedBernoulliLaw
    rw [Measure.pi_singleton, Measure.pi_singleton]
    exact (ENNReal.prod_div_distrib_of_ne_top (fun i _ ↦ measure_ne_top (Q i) {x i})).symm
  have hratios (i : ι) : ((P i {x i} / Q i {x i}).toReal) ≠ 0 := by
    rw [ENNReal.toReal_div]
    exact div_ne_zero (ne_of_gt (ENNReal.toReal_pos (hP i _) (measure_ne_top (P i) _)))
      (ne_of_gt (ENNReal.toReal_pos (hQ i _) (measure_ne_top (Q i) _)))
  rw [MeasureTheory.llr, finite_rnDeriv_apply _ _ hQprod, hratio,
    ENNReal.toReal_prod, Real.log_prod (fun i _ ↦ hratios i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.llr, finite_rnDeriv_apply (P i) (Q i) (hQ i)]

/-- The actual KL divergence of heterogeneous Bernoulli product laws is
the sum of the actual one-coordinate divergences. -/
theorem indexedBernoulliLaw_toReal_klDiv {ι : Type*} [Fintype ι]
    (q p : ι → ℝ≥0) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (hq : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    (InformationTheory.klDiv (indexedBernoulliLaw q (fun i ↦ (hq1 i).le))
      (indexedBernoulliLaw p (fun i ↦ (hp1 i).le))).toReal =
      ∑ i, (InformationTheory.klDiv (PMF.bernoulli (q i) (hq1 i).le).toMeasure
        (PMF.bernoulli (p i) (hp1 i).le).toMeasure).toReal := by
  classical
  let μ := indexedBernoulliLaw q (fun i ↦ (hq1 i).le)
  let ν := indexedBernoulliLaw p (fun i ↦ (hp1 i).le)
  let P (i : ι) := (PMF.bernoulli (q i) (hq1 i).le).toMeasure
  let Q (i : ι) := (PMF.bernoulli (p i) (hp1 i).le).toMeasure
  have hac : μ ≪ ν := finite_fullSupport_ac μ ν (indexedBernoulliLaw_atom_ne_zero p hp hp1)
  have hac' (i : ι) : P i ≪ Q i := bernoulli_measure_ac (q i) (p i) (hp i) (hp1 i) (hq1 i).le
  have heq : μ Set.univ = ν Set.univ := by rw [measure_univ, measure_univ]
  have heq' (i : ι) : P i Set.univ = Q i Set.univ := by rw [measure_univ, measure_univ]
  change (InformationTheory.klDiv μ ν).toReal = ∑ i, (InformationTheory.klDiv (P i) (Q i)).toReal
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac heq]
  simp_rw [InformationTheory.toReal_klDiv_of_measure_eq (hac' _) (heq' _)]
  have hllr : MeasureTheory.llr μ ν = fun x ↦ ∑ i, MeasureTheory.llr (P i) (Q i) (x i) := by
    funext x
    exact indexedBernoulliLaw_llr q p hp hp1 hq hq1 x
  rw [hllr, integral_finset_sum _ (fun i _ ↦ Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i _
  have hm : μ.map (fun x ↦ x i) = P i :=
    (measurePreserving_eval P i).map_eq
  calc
    _ = ∫ b, MeasureTheory.llr (P i) (Q i) b ∂(μ.map (fun x ↦ x i)) :=
      (integral_map (measurable_pi_apply i).aemeasurable
        (MeasureTheory.stronglyMeasurable_llr (P i) (Q i)).aestronglyMeasurable).symm
    _ = _ := by rw [hm]

/-- The product divergence is finite; the real identity does not hide ∞. -/
theorem indexedBernoulliLaw_klDiv_ne_top {ι : Type*} [Fintype ι]
    (q p : ι → ℝ≥0) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (hq1 : ∀ i, q i ≤ 1) :
    InformationTheory.klDiv (indexedBernoulliLaw q hq1)
      (indexedBernoulliLaw p (fun i ↦ (hp1 i).le)) ≠ ⊤ := by
  classical
  apply InformationTheory.klDiv_ne_top_iff.mpr
  exact ⟨finite_fullSupport_ac _ _ (indexedBernoulliLaw_atom_ne_zero p hp hp1),
    Integrable.of_finite⟩

/-- Two changed active rows, with N independent observations each. The two
models swap the Bernoulli parameters on exactly those rows. -/
noncomputable def twoRowSwapLaw (N : ℕ) (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1)
    (alternate : Bool) : Measure ((Fin N × Bool) → Bool) :=
  indexedBernoulliLaw (fun z ↦ if z.2 = alternate then q else p)
    (fun z ↦ by dsimp; split <;> assumption)

/-- Exact KL for two swapped rows, retaining both orientations. -/
theorem twoRowSwapLaw_toReal_klDiv (N : ℕ) (p q : ℝ≥0)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    (InformationTheory.klDiv (twoRowSwapLaw N p q hp1.le hq1.le true)
      (twoRowSwapLaw N p q hp1.le hq1.le false)).toReal =
      N * ((InformationTheory.klDiv (PMF.bernoulli q hq1.le).toMeasure
        (PMF.bernoulli p hp1.le).toMeasure).toReal +
        (InformationTheory.klDiv (PMF.bernoulli p hp1.le).toMeasure
          (PMF.bernoulli q hq1.le).toMeasure).toReal) := by
  classical
  unfold twoRowSwapLaw
  rw [indexedBernoulliLaw_toReal_klDiv]
  · simp [Fintype.sum_prod_type, Finset.sum_add_distrib, mul_add, add_comm]
    change (∑ _ : Fin N, (InformationTheory.klDiv (PMF.bernoulli p hp1.le).toMeasure
      (PMF.bernoulli q hq1.le).toMeasure).toReal) +
      (∑ _ : Fin N, (InformationTheory.klDiv (PMF.bernoulli q hq1.le).toMeasure
        (PMF.bernoulli p hp1.le).toMeasure).toReal) = _
    simp [Finset.sum_const, mul_add]
  all_goals intro z; cases z.2 <;> simp_all

/-- Each direction of the swapped-row KL is bounded with the source's
interior-probability and increment constraints. -/
theorem twoRowSwapLaw_klDiv_le_source (N : ℕ) (p q : ℝ≥0)
    (hp : (1 : ℝ≥0) / 2 ≤ p) (hpq : p < q) (hq1 : q < 1)
    (hhalf : 2 * ((q : ℝ) - (p : ℝ)) ≤ 1 - (p : ℝ)) :
    (InformationTheory.klDiv (twoRowSwapLaw N p q (lt_trans hpq hq1).le hq1.le true)
      (twoRowSwapLaw N p q (lt_trans hpq hq1).le hq1.le false)).toReal ≤
      8 * N * ((q : ℝ) - (p : ℝ)) ^ 2 / (1 - (p : ℝ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : p < 1 := lt_trans hpq hq1
  have hq0 : 0 < q := lt_trans hp0 hpq
  rw [twoRowSwapLaw_toReal_klDiv N p q hp0 hp1 hq0 hq1]
  have hf := bernoulli_toReal_klDiv_le_quadratic q p hp0 hp1 hq0 hq1
  have hr := bernoulli_toReal_klDiv_le_quadratic p q hq0 hq1 hp0 hp1
  let P : ℝ := p
  let Q : ℝ := q
  let X : ℝ := (Q - P) ^ 2
  have hP : (1 : ℝ) / 2 ≤ P := by exact_mod_cast hp
  have hPQ : P < Q := by exact_mod_cast hpq
  have hQ1 : Q < 1 := by exact_mod_cast hq1
  have hP1 : P < 1 := lt_trans hPQ hQ1
  have hX : 0 ≤ X := sq_nonneg _
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := by linarith
  have hqm : 0 < 1 - Q := by linarith
  have hpm : 0 < 1 - P := by linarith
  have hdenf : 1 - P ≤ 2 * (P * (1 - P)) := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * P - 1 by linarith) hpm.le]
  have hdenr : 1 - P ≤ 4 * (Q * (1 - Q)) := by
    have hqhalf : 1 - P ≤ 2 * (1 - Q) := by linarith
    have hm := mul_nonneg (show 0 ≤ 2 * Q - 1 by linarith) hqm.le
    nlinarith
  have hfb : X / (P * (1 - P)) ≤ 2 * X / (1 - P) := by
    apply (div_le_div_iff₀ (by positivity) hpm).2
    nlinarith [mul_nonneg hX (sub_nonneg.mpr hdenf)]
  have hrb : X / (Q * (1 - Q)) ≤ 4 * X / (1 - P) := by
    apply (div_le_div_iff₀ (by positivity) hpm).2
    nlinarith [mul_nonneg hX (sub_nonneg.mpr hdenr)]
  have hsquare : (P - Q) ^ 2 = X := by dsimp [X]; ring
  change (InformationTheory.klDiv (PMF.bernoulli q hq1.le).toMeasure
    (PMF.bernoulli p hp1.le).toMeasure).toReal ≤ X / (P * (1 - P)) at hf
  change (InformationTheory.klDiv (PMF.bernoulli p hp1.le).toMeasure
    (PMF.bernoulli q hq1.le).toMeasure).toReal ≤ (P - Q) ^ 2 / (Q * (1 - Q)) at hr
  rw [hsquare] at hr
  have hsum := add_le_add (hf.trans hfb) (hr.trans hrb)
  have hn : (0 : ℝ) ≤ N := by positivity
  have hm := mul_le_mul_of_nonneg_left hsum hn
  change (N : ℝ) * ((InformationTheory.klDiv (PMF.bernoulli q hq1.le).toMeasure
    (PMF.bernoulli p hp1.le).toMeasure).toReal +
    (InformationTheory.klDiv (PMF.bernoulli p hp1.le).toMeasure
      (PMF.bernoulli q hq1.le).toMeasure).toReal) ≤ 8 * N * X / (1 - P)
  have ht : 0 ≤ (N : ℝ) * (X / (1 - P)) := by positivity
  have heq : (N : ℝ) * (2 * X / (1 - P) + 4 * X / (1 - P)) =
      6 * ((N : ℝ) * (X / (1 - P))) := by ring
  have heq2 : 8 * (N : ℝ) * X / (1 - P) =
      8 * ((N : ℝ) * (X / (1 - P))) := by ring
  rw [heq] at hm
  rw [heq2]
  nlinarith

end StatisticalRL.GenerativeLowerBound

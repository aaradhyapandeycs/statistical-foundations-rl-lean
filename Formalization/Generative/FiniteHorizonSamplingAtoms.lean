import Formalization.Probability.Fano.AssouadWeighted
import Formalization.Generative.FiniteHorizonSamplingDefinitions
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Atoms of the finite-horizon generative sampling law

The generative sampling law `samplingLaw E N` (`generative_model_model_based.tex:23–28`) is a finite
product of transition rows. Here its atoms are computed as products of row probabilities, sums of
atoms are factorized, and the joint law with an independent seed is decomposed over data atoms.
Everything is stated for a general finite state and action type with the sampling module's own
discrete σ-algebra, so it specializes to any carrier without instance bridging.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal

namespace StatisticalRL.FiniteHorizonGenerative

attribute [local instance] ch3FiniteStageStateMeasurable

variable {State Action : Type*} [Fintype State] [Fintype Action]

omit [Fintype State] in
/-- Every set is measurable for the sampling module's discrete σ-algebra. -/
theorem fhlb_measurableSet_state (s : Set State) : MeasurableSet s :=
  MeasurableSpace.measurableSet_top

local instance fhlbStateSingleton : MeasurableSingletonClass State :=
  ⟨fun _ ↦ fhlb_measurableSet_state _⟩

local instance fhlbRowProbability (d : FiniteDistribution State) :
    IsProbabilityMeasure d.rowMeasure :=
  inferInstanceAs (IsProbabilityMeasure d.toPMF.toMeasure)

/-- Atom weight of a data array: the product of the row probabilities of its entries. -/
noncomputable def samplingAtom {H : ℕ} (E : Fin H → EnvironmentStage State Action) (N : ℕ)
    (x : Samples State Action H N) : ℝ :=
  ∏ i : SampleIndex State Action H N, ((E i.1.1).transition i.1.2.1 i.1.2.2).prob (x i)

theorem samplingAtom_nonneg {H : ℕ} (E : Fin H → EnvironmentStage State Action) (N : ℕ)
    (x : Samples State Action H N) : 0 ≤ samplingAtom E N x :=
  Finset.prod_nonneg fun _ _ ↦ FiniteDistribution.prob_nonneg _ _

/-- The singleton mass of the sampling law is the atom weight. -/
theorem samplingLaw_real_singleton {H : ℕ} (E : Fin H → EnvironmentStage State Action) (N : ℕ)
    (x : Samples State Action H N) : (samplingLaw E N).real {x} = samplingAtom E N x := by
  classical
  unfold samplingLaw samplingAtom
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [FiniteDistribution.rowMeasure, PMF.toMeasure_apply_singleton _ _ (fhlb_measurableSet_state _),
    FiniteDistribution.toPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (FiniteDistribution.prob_nonneg _ _)]

/-- Sums of products over data arrays factorize over sample indices. -/
theorem sum_samples_prod_eq {H N : ℕ} [DecidableEq State] [DecidableEq Action]
    (f : SampleIndex State Action H N → State → ℝ) :
    ∑ x : Samples State Action H N, ∏ i, f i (x i) = ∏ i, ∑ y, f i y := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- The atoms sum to one. -/
theorem sum_samplingAtom {H : ℕ} [DecidableEq State] [DecidableEq Action]
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) :
    ∑ x : Samples State Action H N, samplingAtom E N x = 1 := by
  unfold samplingAtom
  rw [sum_samples_prod_eq]
  exact Finset.prod_eq_one fun i _ ↦ FiniteDistribution.sum_prob _

/-- The Bhattacharyya coefficient of two sampling laws is the product of the row coefficients. -/
theorem sum_sqrt_samplingAtom {H : ℕ} [DecidableEq State] [DecidableEq Action]
    (E E' : Fin H → EnvironmentStage State Action) (N : ℕ) :
    ∑ x : Samples State Action H N, Real.sqrt (samplingAtom E N x * samplingAtom E' N x) =
      ∏ i : SampleIndex State Action H N, ∑ y,
        Real.sqrt (((E i.1.1).transition i.1.2.1 i.1.2.2).prob y *
          ((E' i.1.1).transition i.1.2.1 i.1.2.2).prob y) :=
  Assouad.sum_sqrt_prod_eq_prod_sum _ _ (fun _ _ ↦ FiniteDistribution.prob_nonneg _ _)
    (fun _ _ ↦ FiniteDistribution.prob_nonneg _ _)

local instance fhlbSamplesSingleton {H N : ℕ} :
    MeasurableSingletonClass (Samples State Action H N) := inferInstance

/-- A set of (data, seed) pairs whose every data section is measurable is measurable. -/
theorem measurableSet_of_sections {H N : ℕ} [Finite State] {Seed : Type*} [MeasurableSpace Seed]
    (P : Samples State Action H N → Seed → Prop) (hP : ∀ x, MeasurableSet {ω | P x ω}) :
    MeasurableSet {p : Samples State Action H N × Seed | P p.1 p.2} := by
  have : {p : Samples State Action H N × Seed | P p.1 p.2} =
      ⋃ x, ({x} : Set (Samples State Action H N)) ×ˢ {ω | P x ω} := by
    ext ⟨x, ω⟩
    simp
  rw [this]
  exact MeasurableSet.iUnion fun x ↦ (measurableSet_singleton x).prod (hP x)

/-- **Joint law of data and an independent seed.** The probability of an event is the
atom-weighted sum of the seed probabilities of its data sections. -/
theorem samplingLaw_prod_real {H N : ℕ} [DecidableEq State] [DecidableEq Action]
    (E : Fin H → EnvironmentStage State Action) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (P : Samples State Action H N → Seed → Prop) (hP : ∀ x, MeasurableSet {ω | P x ω}) :
    ((samplingLaw E N).prod ν).real {p | P p.1 p.2} =
      ∑ x, samplingAtom E N x * ν.real {ω | P x ω} := by
  haveI : IsProbabilityMeasure (samplingLaw E N) := by
    unfold samplingLaw; infer_instance
  rw [measureReal_def, Measure.prod_apply (measurableSet_of_sections P hP), lintegral_fintype,
    ENNReal.toReal_sum (fun x _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, samplingLaw_real_singleton,
    mul_comm]
  rfl

end StatisticalRL.FiniteHorizonGenerative

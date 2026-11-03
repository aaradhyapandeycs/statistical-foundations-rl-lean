import Formalization.Generative.GenerativeLowerBoundFamilyObservation

/-! Actual indexed-family sample KL through the common reconstruction. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance familyKLStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance familyKLFinMeasurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- Injective maps between finite discrete spaces are measurable embeddings. -/
theorem finite_measurableEmbedding {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSingletonClass Ω]
    [MeasurableSingletonClass Ξ] (f : Ω → Ξ) (hf : Function.Injective f) :
    MeasurableEmbedding f := by
  exact ⟨hf, measurable_of_countable _, fun s _ ↦ (Set.to_countable (f '' s)).measurableSet⟩

/-- Mapping both finite probability measures through one injective encoding
preserves true relative entropy, when the source measures are absolutely
continuous in the stated orientation. -/
theorem finite_klDiv_map_injective {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSingletonClass Ω]
    [MeasurableSingletonClass Ξ] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν)
    (f : Ω → Ξ) (hf : Function.Injective f) :
    (InformationTheory.klDiv (μ.map f) (ν.map f)).toReal =
      (InformationTheory.klDiv μ ν).toReal := by
  classical
  have he := finite_measurableEmbedding f hf
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map he.measurable.aemeasurable
  letI : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map he.measurable.aemeasurable
  have hmap : μ.map f ≪ ν.map f := he.absolutelyContinuous_map hμν
  have hu : μ Set.univ = ν Set.univ := by rw [measure_univ, measure_univ]
  have hum : (μ.map f) Set.univ = (ν.map f) Set.univ := by rw [measure_univ, measure_univ]
  rw [InformationTheory.toReal_klDiv_of_measure_eq hmap hum,
    InformationTheory.toReal_klDiv_of_measure_eq hμν hu]
  rw [he.integral_map]
  apply integral_congr_ae
  filter_upwards [hμν.ae_le (he.rnDeriv_map μ ν)] with x hx
  simp only [MeasureTheory.llr, hx]

/-- Both actual divergences are finite; their real equality does not hide ∞. -/
theorem finite_klDiv_map_injective_ne_top {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSingletonClass Ω]
    [MeasurableSingletonClass Ξ] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν)
    (f : Ω → Ξ) (hf : Function.Injective f) :
    InformationTheory.klDiv μ ν ≠ ⊤ ∧ InformationTheory.klDiv (μ.map f) (ν.map f) ≠ ⊤ := by
  classical
  have he := finite_measurableEmbedding f hf
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map he.measurable.aemeasurable
  constructor
  · exact InformationTheory.klDiv_ne_top_iff.mpr ⟨hμν, Integrable.of_finite⟩
  · exact InformationTheory.klDiv_ne_top_iff.mpr ⟨he.absolutelyContinuous_map hμν, Integrable.of_finite⟩

/-- Source family parameters are interior whenever both row probabilities
are interior. -/
theorem familyBernoulliParameter_pos {m n N : ℕ} (i : HardFamilyIndex m n)
    (p q : ℝ≥0) (hp : 0 < p) (hq : 0 < q) :
    ∀ z : FamilyActiveCoordinates m n N, 0 < familyBernoulliParameter (N := N) i p q z := by
  intro z
  unfold familyBernoulliParameter
  split <;> assumption

theorem familyBernoulliParameter_lt_one {m n N : ℕ} (i : HardFamilyIndex m n)
    (p q : ℝ≥0) (hp : p < 1) (hq : q < 1) :
    ∀ z : FamilyActiveCoordinates m n N, familyBernoulliParameter (N := N) i p q z < 1 := by
  intro z
  unfold familyBernoulliParameter
  split <;> assumption

/-- Actual indexed-model full-array KL is the KL of their heterogeneous
Bernoulli indicator products, in the same first-to-second orientation. -/
theorem familySamplingLaw_klDiv_eq_indexedProduct {m n : ℕ}
    (i j : HardFamilyIndex m n) (γ : ℝ) (p q : ℝ≥0)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) (N : ℕ) :
    let Mᵢ := familyMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    let Mⱼ := familyMDP j γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    (InformationTheory.klDiv (samplingLaw Mᵢ N) (samplingLaw Mⱼ N)).toReal =
      (InformationTheory.klDiv
        (indexedBernoulliLaw (familyBernoulliParameter (N := N) i p q)
          (familyBernoulliParameter_le_one (N := N) i p q (le_trans hpq hq.le) hq.le))
        (indexedBernoulliLaw (familyBernoulliParameter (N := N) j p q)
          (familyBernoulliParameter_le_one (N := N) j p q (le_trans hpq hq.le) hq.le))).toReal := by
  classical
  let u : FamilyActiveCoordinates m n N → ℝ≥0 := familyBernoulliParameter (N := N) i p q
  let v : FamilyActiveCoordinates m n N → ℝ≥0 := familyBernoulliParameter (N := N) j p q
  have hp1 : p < 1 := lt_of_le_of_lt hpq hq
  have hq0 : 0 < q := lt_of_lt_of_le hp hpq
  have hu0 : ∀ z, 0 < u z := familyBernoulliParameter_pos i p q hp hq0
  have hv0 : ∀ z, 0 < v z := familyBernoulliParameter_pos j p q hp hq0
  have hu1 : ∀ z, u z < 1 := familyBernoulliParameter_lt_one i p q hp1 hq
  have hv1 : ∀ z, v z < 1 := familyBernoulliParameter_lt_one j p q hp1 hq
  let μ := indexedBernoulliLaw u (fun z ↦ (hu1 z).le)
  let ν := indexedBernoulliLaw v (fun z ↦ (hv1 z).le)
  have hac : μ ≪ ν := finite_fullSupport_ac μ ν (indexedBernoulliLaw_atom_ne_zero v hv0 hv1)
  have he := finite_klDiv_map_injective μ ν hac familyReconstruct familyReconstruct_injective
  dsimp only
  rw [familySamplingLaw_eq_reconstructed_product i γ p q hγ hγ1 hpq hq N,
    familySamplingLaw_eq_reconstructed_product j γ p q hγ hγ1 hpq hq N]
  exact he

/-- The actual full-array KL has the exact sum of one-coordinate Bernoulli
KLs, with the indexed first-to-second model orientation. -/
theorem familySamplingLaw_klDiv_eq_coordinate_sum {m n : ℕ}
    (i j : HardFamilyIndex m n) (γ : ℝ) (p q : ℝ≥0)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) (N : ℕ) :
    let Mᵢ := familyMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    let Mⱼ := familyMDP j γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    (InformationTheory.klDiv (samplingLaw Mᵢ N) (samplingLaw Mⱼ N)).toReal =
      ∑ z : FamilyActiveCoordinates m n N,
        (InformationTheory.klDiv
          (PMF.bernoulli (familyBernoulliParameter (N := N) i p q z)
            (familyBernoulliParameter_le_one (N := N) i p q (le_trans hpq hq.le) hq.le z)).toMeasure
          (PMF.bernoulli (familyBernoulliParameter (N := N) j p q z)
            (familyBernoulliParameter_le_one (N := N) j p q (le_trans hpq hq.le) hq.le z)).toMeasure).toReal := by
  classical
  have hp1 : p < 1 := lt_of_le_of_lt hpq hq
  have hq0 : 0 < q := lt_of_lt_of_le hp hpq
  dsimp only
  rw [familySamplingLaw_klDiv_eq_indexedProduct i j γ p q hγ hγ1 hp hpq hq N]
  exact indexedBernoulliLaw_toReal_klDiv _ _
    (familyBernoulliParameter_pos j p q hp hq0)
    (familyBernoulliParameter_lt_one j p q hp1 hq)
    (familyBernoulliParameter_pos i p q hp hq0)
    (familyBernoulliParameter_lt_one i p q hp1 hq)

/-- The actual full-array relative entropy is finite in this orientation. -/
theorem familySamplingLaw_klDiv_ne_top {m n : ℕ}
    (i j : HardFamilyIndex m n) (γ : ℝ) (p q : ℝ≥0)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) (N : ℕ) :
    let Mᵢ := familyMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    let Mⱼ := familyMDP j γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    InformationTheory.klDiv (samplingLaw Mᵢ N) (samplingLaw Mⱼ N) ≠ ⊤ := by
  classical
  let u : FamilyActiveCoordinates m n N → ℝ≥0 := familyBernoulliParameter (N := N) i p q
  let v : FamilyActiveCoordinates m n N → ℝ≥0 := familyBernoulliParameter (N := N) j p q
  have hp1 : p < 1 := lt_of_le_of_lt hpq hq
  have hq0 : 0 < q := lt_of_lt_of_le hp hpq
  have hu1 : ∀ z, u z < 1 := familyBernoulliParameter_lt_one i p q hp1 hq
  have hv0 : ∀ z, 0 < v z := familyBernoulliParameter_pos j p q hp hq0
  have hv1 : ∀ z, v z < 1 := familyBernoulliParameter_lt_one j p q hp1 hq
  let μ := indexedBernoulliLaw u (fun z ↦ (hu1 z).le)
  let ν := indexedBernoulliLaw v (fun z ↦ (hv1 z).le)
  have hac : μ ≪ ν := finite_fullSupport_ac μ ν (indexedBernoulliLaw_atom_ne_zero v hv0 hv1)
  have he := (finite_klDiv_map_injective_ne_top μ ν hac familyReconstruct familyReconstruct_injective).2
  dsimp only
  rw [familySamplingLaw_eq_reconstructed_product i γ p q hγ hγ1 hpq hq N,
    familySamplingLaw_eq_reconstructed_product j γ p q hγ hγ1 hpq hq N]
  exact he

end StatisticalRL.GenerativeLowerBound

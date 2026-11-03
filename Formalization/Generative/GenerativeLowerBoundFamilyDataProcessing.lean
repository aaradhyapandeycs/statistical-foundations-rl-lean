import Formalization.Generative.GenerativeLowerBoundFiniteKLDataProcessing
import Formalization.Generative.GenerativeLowerBoundFamilyKL

/-! Data processing for actual indexed-family complete sample arrays. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance familyDPStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance familyDPFinMeasurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- Any common finite-valued statistic of the complete observation has no
larger KL than the actual indexed-family observation law. The complete arrays
need not have full support: deterministic rows are reconstructed from the
full-support active-coordinate Bernoulli product. -/
theorem familySamplingLaw_klDiv_map_le {m n : ℕ}
    (i j : HardFamilyIndex m n) (γ : ℝ) (p q : ℝ≥0)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) (N : ℕ)
    {Ξ : Type*} [Fintype Ξ] [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (f : Samples (Option (Fin m)) (Fin (n + 1)) N → Ξ) :
    let Mᵢ := familyMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    let Mⱼ := familyMDP j γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    (InformationTheory.klDiv ((samplingLaw Mᵢ N).map f) ((samplingLaw Mⱼ N).map f)).toReal ≤
      (InformationTheory.klDiv (samplingLaw Mᵢ N) (samplingLaw Mⱼ N)).toReal := by
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
  have hμ := indexedBernoulliLaw_atom_ne_zero u hu0 hu1
  have hν := indexedBernoulliLaw_atom_ne_zero v hv0 hv1
  have hc := finite_klDiv_map_le μ ν hμ hν (f ∘ familyReconstruct)
  have he := finite_klDiv_map_injective μ ν (finite_fullSupport_ac μ ν hν)
    familyReconstruct familyReconstruct_injective
  dsimp only
  rw [familySamplingLaw_eq_reconstructed_product i γ p q hγ hγ1 hpq hq N,
    familySamplingLaw_eq_reconstructed_product j γ p q hγ hγ1 hpq hq N]
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _), he]
  exact hc

end StatisticalRL.GenerativeLowerBound

import Formalization.Generative.GenerativeLowerBoundQRandomMixture

/-! Common arbitrary-output kernel under a deterministic data encoding. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- A model-independent reconstruction transfers the entire probability of
an output event for a common arbitrary measurable-output kernel. -/
theorem finiteDataRandomOutputLaw_map_event {X Z Y : Type*} [Fintype X] [Fintype Z]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Z) (κ : Z → Measure Y)
    [∀ z, IsProbabilityMeasure (κ z)] (E : Set Y) (hE : MeasurableSet E) :
    (finiteDataRandomOutputLaw (μ.map f) κ).real (Set.univ ×ˢ E) =
      (finiteDataRandomOutputLaw μ (fun x ↦ κ (f x))).real (Set.univ ×ˢ E) := by
  classical
  have hf : Measurable f := measurable_of_countable _
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  rw [finiteDataRandomOutputLaw_real_event _ κ E hE,
    finiteDataRandomOutputLaw_real_event _ (fun x ↦ κ (f x)) E hE]
  have hmap := integral_map hf.aemeasurable
    (show AEStronglyMeasurable (fun z : Z ↦ (κ z).real E) (μ.map f) from
      (measurable_of_countable _).aestronglyMeasurable)
  rw [integral_fintype _ Integrable.of_finite, integral_fintype _ Integrable.of_finite] at hmap
  simpa [smul_eq_mul, mul_comm] using hmap

end StatisticalRL.GenerativeLowerBound

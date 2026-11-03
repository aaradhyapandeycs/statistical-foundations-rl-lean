import Formalization.Generative.GenerativeLowerBoundQEstimatorBinaryKernel
import Mathlib.MeasureTheory.Measure.Prod

/-! Actual joint laws for finite observations and general measurable outputs. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

section
variable {X Y : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Y]

/-- The genuine data/output joint law for one common family of conditional
output laws. The output type Y need not be finite or countable. -/
noncomputable def finiteDataRandomOutputLaw (μ : Measure X) (κ : X → Measure Y) : Measure (X × Y) :=
  ∑ x, μ {x} • ((Measure.dirac x).prod (κ x))

/-- The joint data/output law is a probability law for every model. -/
instance finiteDataRandomOutputLaw_probability (μ : Measure X) (κ : X → Measure Y)
    [IsProbabilityMeasure μ] [∀ x, IsProbabilityMeasure (κ x)] :
    IsProbabilityMeasure (finiteDataRandomOutputLaw μ κ) := by
  constructor
  classical
  simp only [finiteDataRandomOutputLaw, Measure.finset_sum_apply, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one]
  simpa using (sum_measure_singleton (μ := μ) (s := Finset.univ))

/-- A measurable output event has the actual conditional-mixture probability
under the joint experiment. -/
theorem finiteDataRandomOutputLaw_event (μ : Measure X) (κ : X → Measure Y)
    [IsProbabilityMeasure μ] [∀ x, IsProbabilityMeasure (κ x)]
    (E : Set Y) (hE : MeasurableSet E) :
    finiteDataRandomOutputLaw μ κ (Set.univ ×ˢ E) = ∑ x, μ {x} * (κ x) E := by
  classical
  unfold finiteDataRandomOutputLaw
  rw [Measure.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp [Measure.smul_apply, Measure.prod_prod, hE]

/-- Strict baseline-distance test true is exactly baseline-output loss under
the same common output kernel. -/
theorem finiteDataRandomOutputLaw_binary_true (μ : Measure X) (κ : X → Measure Y)
    [IsProbabilityMeasure μ] [∀ x, IsProbabilityMeasure (κ x)]
    (E : Set Y) (hE : MeasurableSet E) :
    (outputEventBinaryJointLaw μ κ E) (Set.univ ×ˢ {true}) =
      finiteDataRandomOutputLaw μ κ (Set.univ ×ˢ E) := by
  classical
  rw [finiteDataRandomOutputLaw_event μ κ E hE]
  unfold outputEventBinaryJointLaw finiteKernelJointLaw
  rw [PMF.toMeasure_bind_apply _ _ _ (MeasurableSet.univ.prod (measurableSet_singleton _)), tsum_fintype]
  apply Finset.sum_congr rfl
  intro x _
  rw [Measure.toPMF_apply]
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  rw [Measure.map_apply (measurable_of_countable _) (MeasurableSet.univ.prod (measurableSet_singleton _))]
  simpa using congrArg (fun t : ℝ≥0∞ ↦ μ {x} * t) (outputEventBinaryKernel_true κ E x)

end
end StatisticalRL.GenerativeLowerBound

namespace StatisticalRL.GenerativeLowerBound
open MeasureTheory

/-- A fixed alternative's strict risk event contains the baseline acceptance
ball, even for an arbitrary measurable output distribution. -/
theorem baseline_acceptance_probability_le_alternative_risk
    {Y : Type*} [NormedAddCommGroup Y] [MeasurableSpace Y]
    (ρ : Measure Y) [IsProbabilityMeasure ρ] (v₀ v₁ : Y) (ε : ℝ)
    (hsep : 2 * ε < ‖v₁ - v₀‖) :
    ρ.real {v | ‖v - v₀‖ ≤ ε} ≤ ρ.real {v | ε < ‖v - v₁‖} := by
  apply measureReal_mono _ (measure_ne_top _ _)
  intro v hv
  change ‖v - v₀‖ ≤ ε at hv
  change ε < ‖v - v₁‖
  have htri : ‖v₁ - v₀‖ ≤ ‖v - v₁‖ + ‖v - v₀‖ := by
    have h := norm_add_le (v₁ - v) (v - v₀)
    simpa [sub_add_sub_cancel, norm_sub_rev] using h
  linarith

end StatisticalRL.GenerativeLowerBound

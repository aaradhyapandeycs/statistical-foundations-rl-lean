import Formalization.Generative.GenerativeLowerBoundFiniteKernelSeed

/-! Binary reduction for arbitrary measurable real-valued Q-output laws. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

section
variable {X Y : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Y]

/-- Probability that the randomized estimator output falls in a measurable
event, represented as an NNReal Bernoulli parameter. -/
noncomputable def outputEventProbability (κ : X → Measure Y)
    [∀ x, IsProbabilityMeasure (κ x)] (E : Set Y) (x : X) : ℝ≥0 :=
  ((κ x) E).toNNReal

theorem outputEventProbability_le_one (κ : X → Measure Y)
    [∀ x, IsProbabilityMeasure (κ x)] (E : Set Y) (x : X) :
    outputEventProbability κ E x ≤ 1 := by
  unfold outputEventProbability
  have h : (κ x) E ≤ 1 := by
    calc
      (κ x) E ≤ (κ x) Set.univ := measure_mono (Set.subset_univ E)
      _ = 1 := measure_univ
  simpa using ENNReal.toNNReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) h

/-- The binary kernel records whether the *same* randomized Q output lies in
one fixed baseline-distance event; it is independent of model index. -/
noncomputable def outputEventBinaryKernel (κ : X → Measure Y)
    [∀ x, IsProbabilityMeasure (κ x)] (E : Set Y) (x : X) : PMF Bool :=
  PMF.bernoulli (outputEventProbability κ E x) (outputEventProbability_le_one κ E x)

/-- The induced binary kernel has exactly the event probability of the
possibly infinite-valued output law, without any finite-output assumption. -/
theorem outputEventBinaryKernel_true (κ : X → Measure Y)
    [∀ x, IsProbabilityMeasure (κ x)] (E : Set Y) (x : X) :
    (outputEventBinaryKernel κ E x).toMeasure {true} = (κ x) E := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [outputEventBinaryKernel, outputEventProbability, PMF.bernoulli_apply,
    ENNReal.coe_toNNReal (measure_ne_top _ _)]

/-- The actual joint experiment of finite data and its induced binary test. -/
noncomputable def outputEventBinaryJointLaw (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : X → Measure Y) [∀ x, IsProbabilityMeasure (κ x)] (E : Set Y) : Measure (X × Bool) :=
  finiteKernelJointLaw μ (outputEventBinaryKernel κ E)

end
end StatisticalRL.GenerativeLowerBound

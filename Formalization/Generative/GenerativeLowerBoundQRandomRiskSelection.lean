import Formalization.Generative.GenerativeLowerBoundRandomBinaryTesting
import Formalization.Generative.GenerativeLowerBoundQMixtureTesting

/-! Common arbitrary-output-kernel baseline/mixture risk selection. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

/-- The false output of the binary kernel is the probability of the
complement of the fixed output event. -/
theorem outputEventBinaryKernel_false {X Y : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [MeasurableSpace Y] (κ : X → Measure Y)
    [∀ x, IsProbabilityMeasure (κ x)] (E : Set Y) (hE : MeasurableSet E) (x : X) :
    (outputEventBinaryKernel κ E x).toMeasure {false} = (κ x) Eᶜ := by
  have h := outputEventBinaryKernel_true κ E x
  have hfalse : ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by ext b; cases b <;> simp
  rw [hfalse, measure_compl (measurableSet_singleton true) (measure_ne_top _ _)]
  rw [measure_compl hE (measure_ne_top _ _)]
  simp only [measure_univ]
  exact congrArg (fun t : ℝ≥0∞ ↦ 1 - t) h

/-- The actual binary-test error under a model is the actual Q-output
probability of the baseline acceptance event. -/
theorem outputEventBinaryJointLaw_false {X Y : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y]
    (μ : Measure X) (κ : X → Measure Y) [IsProbabilityMeasure μ]
    [∀ x, IsProbabilityMeasure (κ x)] (E : Set Y) (hE : MeasurableSet E) :
    (outputEventBinaryJointLaw μ κ E) (Set.univ ×ˢ {false}) =
      finiteDataRandomOutputLaw μ κ (Set.univ ×ˢ Eᶜ) := by
  classical
  rw [finiteDataRandomOutputLaw_event μ κ Eᶜ hE.compl]
  unfold outputEventBinaryJointLaw finiteKernelJointLaw
  rw [PMF.toMeasure_bind_apply _ _ _ (MeasurableSet.univ.prod (measurableSet_singleton _)), tsum_fintype]
  apply Finset.sum_congr rfl
  intro x _
  rw [Measure.toPMF_apply]
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  rw [Measure.map_apply (measurable_of_countable _) (MeasurableSet.univ.prod (measurableSet_singleton _))]
  simpa using congrArg (fun t : ℝ≥0∞ ↦ μ {x} * t) (outputEventBinaryKernel_false κ E hE x)

/-- On any alternative, the common induced binary false-error probability is
bounded by the actual randomized-output strict risk. -/
theorem randomOutput_binary_false_le_risk {X Y : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [NormedAddCommGroup Y]
    [MeasurableSpace Y] (μ : Measure X) (κ : X → Measure Y) [IsProbabilityMeasure μ]
    [∀ x, IsProbabilityMeasure (κ x)] (v₀ v₁ : Y) (ε : ℝ)
    (hsep : 2 * ε < ‖v₁ - v₀‖)
    (hE : MeasurableSet {v : Y | ε < ‖v - v₀‖}) :
    (outputEventBinaryJointLaw μ κ {v : Y | ε < ‖v - v₀‖}).real
        (Set.univ ×ˢ {false}) ≤
      (finiteDataRandomOutputLaw μ κ).real
        (Set.univ ×ˢ {v : Y | ε < ‖v - v₁‖}) := by
  rw [measureReal_def, outputEventBinaryJointLaw_false μ κ _ hE]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro z hz
  rcases hz with ⟨_, hz⟩
  have hh : ‖z.2 - v₀‖ ≤ ε := le_of_not_gt hz
  have htri : ‖v₁ - v₀‖ ≤ ‖z.2 - v₁‖ + ‖z.2 - v₀‖ := by
    have h := norm_add_le (v₁ - z.2) (z.2 - v₀)
    simpa [sub_add_sub_cancel, norm_sub_rev] using h
  refine ⟨Set.mem_univ _, ?_⟩
  change ε < ‖z.2 - v₁‖
  linarith

end StatisticalRL.GenerativeLowerBound
